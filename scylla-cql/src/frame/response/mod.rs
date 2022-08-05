pub mod authenticate;
pub mod cql_to_rust;
pub mod error;
pub mod event;
pub mod raw_result;
pub mod result;
pub mod supported;

use crate::frame::frame_errors::ParseError;
use bytes::Bytes;
use num_enum::TryFromPrimitive;

pub use error::Error;
pub use supported::Supported;

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, TryFromPrimitive)]
#[repr(u8)]
pub enum ResponseOpcode {
    Error = 0x00,
    Ready = 0x02,
    Authenticate = 0x03,
    Supported = 0x06,
    Result = 0x08,
    Event = 0x0C,
    AuthChallenge = 0x0E,
    AuthSuccess = 0x10,
}

#[derive(Debug)]
pub enum Response {
    Error(Error),
    Ready,
    Result(result::Result),
    Authenticate(authenticate::Authenticate),
    AuthSuccess(authenticate::AuthSuccess),
    AuthChallenge(authenticate::AuthChallenge),
    Supported(Supported),
    Event(event::Event),
}

impl Response {
    pub fn deserialize(opcode: ResponseOpcode, byts: Bytes) -> Result<Response, ParseError> {
        let buf = &mut &*byts;
        let response = match opcode {
            ResponseOpcode::Error => Response::Error(Error::deserialize(buf)?),
            ResponseOpcode::Ready => Response::Ready,
            ResponseOpcode::Authenticate => {
                Response::Authenticate(authenticate::Authenticate::deserialize(buf)?)
            }
            ResponseOpcode::Supported => Response::Supported(Supported::deserialize(buf)?),
            ResponseOpcode::Result => Response::Result(result::deserialize(byts)?),
            ResponseOpcode::Event => Response::Event(event::Event::deserialize(buf)?),
            ResponseOpcode::AuthChallenge => {
                Response::AuthChallenge(authenticate::AuthChallenge::deserialize(buf)?)
            }
            ResponseOpcode::AuthSuccess => {
                Response::AuthSuccess(authenticate::AuthSuccess::deserialize(buf)?)
            }
        };

        Ok(response)
    }
}
