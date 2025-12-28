use std::pin::Pin;
use std::task::{Context, Poll, Waker};

use tokio::time::{Instant, Sleep};

/// A possibly-infinite [`Sleep`].
///
/// This is a version of [`tokio::time::Sleep`] that allows to explicitly sleep
/// for an indefinite amount of time, and which implements the infinite sleep
/// efficiently.
///
/// While an infinite sleep can just be simulated by sleeping for a very long
/// duration (e.g. years), this still requires registering the future's timer
/// in tokio runtime's internal data structures, which requires taking a lock
/// when the future is polled for the first time.
///
/// This future is meant to be used in rather niche contexts where the deadline
/// is reset quite frequently and optimizing the infinite wait case makes sense.
/// Specifically, the future is meant to be used in the implementation
/// of client-side timeouts, where the connection router tracks the earliest
/// deadline of all in-flight requests.
//
// Implementation note:
// The structure effectively has two states: infinite sleep or finite sleep.
// If `infinite` is `Some`, then the sleep is infinite, otherwise it is finite
// and defined by the `finite` future.
// Why not use `enum` to clearly indicate the two states? The answer is the
// `finite` future. First, it registers a timer which needs to be unregistered
// on destruction - re-registering the timer can be cheaper in some cases.
// Second, because the `Sleep` future needs pinning, we want to avoid having
// to allocate the box again and again.
pub(crate) struct MaybeInfiniteSleep {
    infinite: Option<Option<Waker>>,
    finite: Pin<Box<Sleep>>,
}

impl MaybeInfiniteSleep {
    pub(crate) fn new_infinite() -> Self {
        Self {
            infinite: Some(None),
            finite: Box::pin(tokio::time::sleep_until(Instant::now())),
        }
    }

    pub(crate) fn is_elapsed(&self) -> bool {
        self.infinite.is_none() && self.finite.is_elapsed()
    }

    pub(crate) fn deadline(&self) -> Option<Instant> {
        self.infinite.is_none().then(|| self.finite.deadline())
    }

    pub(crate) fn reset(&mut self, deadline: Option<Instant>) {
        match deadline {
            Some(deadline) => {
                // Wake the waker to let it properly register in `self.finite`,
                // also reset the `self.infinite` field
                if let Some(Some(waker)) = self.infinite.take() {
                    waker.wake();
                }
                self.finite.as_mut().reset(deadline);
            }
            None => {
                if self.infinite.is_none() {
                    // Note: the `finite` timer future might have been polled
                    // and it might have stored some waker, which will be
                    // awoken at the previous deadline. This is fine - the task
                    // will be spuriously woken up, but polling again will
                    // properly register the waker in `self.infinite`.
                    self.infinite = Some(None);
                }
            }
        }
    }
}

impl Future for MaybeInfiniteSleep {
    type Output = ();

    fn poll(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        let mut me = self.as_mut();
        match &mut me.infinite {
            Some(Some(waker)) => {
                waker.clone_from(cx.waker());
                Poll::Pending
            }
            Some(maybe_waker @ None) => {
                *maybe_waker = Some(cx.waker().clone());
                Poll::Pending
            }
            None => me.finite.as_mut().poll(cx),
        }
    }
}

#[cfg(test)]
mod tests {
    use std::sync::atomic::{AtomicUsize, Ordering};
    use std::sync::{Arc, Mutex};
    use std::time::Duration;

    use futures::task::ArcWake;

    use super::*;

    struct CountingWaker {
        count: AtomicUsize,
    }

    impl CountingWaker {
        fn new() -> Self {
            Self {
                count: AtomicUsize::new(0),
            }
        }

        fn wake_count(&self) -> usize {
            self.count.load(Ordering::Relaxed)
        }
    }

    impl ArcWake for CountingWaker {
        fn wake_by_ref(arc_self: &Arc<Self>) {
            arc_self.count.fetch_add(1, Ordering::Relaxed);
        }
    }

    fn poll_with_waker<F>(fut: &mut F) -> (Poll<F::Output>, Arc<CountingWaker>)
    where
        F: Future + Unpin,
    {
        let cwaker = Arc::new(CountingWaker::new());
        let waker = futures::task::waker_ref(&cwaker);
        let mut cx = Context::from_waker(&waker);
        let poll_result = Pin::new(fut).poll(&mut cx);
        (poll_result, cwaker)
    }

    #[tokio::test]
    async fn simple_infinite_sleep() {
        // Check that a simple scenario with an infinite sleep works correctly
        // and does not trigger the waker.

        tokio::time::pause();

        let mut fut = MaybeInfiniteSleep::new_infinite();
        assert!(!fut.is_elapsed());
        assert!(fut.deadline().is_none());

        let (poll, waker) = poll_with_waker(&mut fut);
        assert!(matches!(poll, Poll::Pending));
        assert_eq!(waker.wake_count(), 0);

        tokio::time::advance(Duration::from_secs(1)).await;
        assert_eq!(waker.wake_count(), 0);

        let (poll, waker) = poll_with_waker(&mut fut);
        assert!(matches!(poll, Poll::Pending));
        assert_eq!(waker.wake_count(), 0);
        assert!(!fut.is_elapsed());
        assert!(fut.deadline().is_none());
    }

    #[tokio::test]
    async fn infinite_to_finite_switch_wakes_task() {
        // Check that resetting a timer from infinite state to finite
        // will wake the task.

        tokio::time::pause();

        let mut fut = MaybeInfiniteSleep::new_infinite();

        let (poll, waker) = poll_with_waker(&mut fut);
        assert!(matches!(poll, Poll::Pending));
        assert_eq!(waker.wake_count(), 0);

        // Resetting after polling should wake the current waker
        // so that the task can register its waker in the `Sleep` future properly
        let deadline = Instant::now() + Duration::from_secs(1);
        fut.reset(Some(deadline));
        assert!(!fut.is_elapsed());
        assert_eq!(fut.deadline(), Some(deadline));
        assert_eq!(waker.wake_count(), 1);
    }

    #[tokio::test]
    async fn state_change() {
        // Checks that resetting puts the timer future into the correct state,
        // regardless of the previous state.

        tokio::time::pause();

        let pre_timeout_configs = [
            ("infinite", None),
            ("finite (short)", Some(Duration::from_secs(1))),
            ("finite (long)", Some(Duration::from_secs(3))),
        ];

        let poll_configs = [("without polling", false), ("with polling", true)];

        let post_timeout_configs = [("infinite", None), ("finite", Some(Duration::from_secs(2)))];

        for (pre_name, pre_timeout) in pre_timeout_configs.iter() {
            for (post_name, post_timeout) in post_timeout_configs.iter() {
                for (poll_name, with_poll) in poll_configs.iter() {
                    println!(
                        "Test case: {pre_name} pre-timeout, {poll_name}, {post_name} post-timeout"
                    );

                    let mut fut = MaybeInfiniteSleep::new_infinite();
                    fut.reset(pre_timeout.map(|t| Instant::now() + t));

                    if *with_poll {
                        let (poll, _) = poll_with_waker(&mut fut);
                        assert!(matches!(poll, Poll::Pending));
                    }

                    match post_timeout {
                        None => {
                            fut.reset(None);
                            assert!(!fut.is_elapsed());
                            assert_eq!(fut.deadline(), None);

                            tokio::time::advance(Duration::from_secs(1)).await;

                            assert!(!fut.is_elapsed());
                            assert_eq!(fut.deadline(), None);

                            let (poll, _) = poll_with_waker(&mut fut);
                            assert!(matches!(poll, Poll::Pending));
                        }
                        Some(timeout) => {
                            let deadline = Instant::now() + *timeout;
                            fut.reset(Some(deadline));
                            assert!(!fut.is_elapsed());
                            assert_eq!(fut.deadline(), Some(deadline));

                            tokio::time::advance(*timeout - Duration::from_millis(500)).await;

                            assert!(!fut.is_elapsed());
                            assert_eq!(fut.deadline(), Some(deadline));

                            let (poll, _) = poll_with_waker(&mut fut);
                            assert!(matches!(poll, Poll::Pending));

                            tokio::time::advance(Duration::from_secs(1)).await;

                            assert!(fut.is_elapsed());
                            assert_eq!(fut.deadline(), Some(deadline));

                            let (poll, _) = poll_with_waker(&mut fut);
                            assert!(matches!(poll, Poll::Ready(_)));
                        }
                    }
                }
            }
        }
    }

    #[tokio::test]
    async fn finite_timeout_properly_polled_to_completion() {
        // Checks that the future will be properly polled to completion in a task,
        // after a reset. In contrast to `state_change`, this test does not poll
        // the future manually, so proper completion of the task relies on
        // the future waking the task at appropriate moments.

        tokio::time::pause();

        let pre_configs = [
            ("infinite", None),
            ("finite (short)", Some(Duration::from_secs(1))),
            ("finite (long)", Some(Duration::from_secs(3))),
        ];

        let poll_configs = [
            ("without initial polling", false),
            ("with initial polling", true),
        ];

        for (config_name, pre_timeout) in pre_configs.iter() {
            for (poll_name, with_poll) in poll_configs.iter() {
                println!("Test case: {config_name}, {poll_name}");

                let mut fut = MaybeInfiniteSleep::new_infinite();
                fut.reset(pre_timeout.map(|t| Instant::now() + t));

                let shared_fut = Arc::new(Mutex::new(fut));

                let handle = tokio::task::spawn({
                    let shared_fut = Arc::clone(&shared_fut);
                    std::future::poll_fn(move |cx| {
                        Pin::new(shared_fut.try_lock().unwrap()).as_mut().poll(cx)
                    })
                });

                if *with_poll {
                    tokio::task::yield_now().await;
                }

                shared_fut
                    .try_lock()
                    .unwrap()
                    .reset(Some(Instant::now() + Duration::from_secs(2)));

                tokio::task::yield_now().await;
                assert!(!shared_fut.try_lock().unwrap().is_elapsed());

                tokio::time::advance(Duration::from_millis(1500)).await;
                assert!(!shared_fut.try_lock().unwrap().is_elapsed());

                tokio::time::advance(Duration::from_millis(1500)).await;
                tokio::task::yield_now().await;
                assert!(shared_fut.try_lock().unwrap().is_elapsed());
                assert!(handle.is_finished());
            }
        }
    }
}
