use super::*;

#[derive(Debug, Clone, PartialEq)]
pub enum Error {
  Empty,
}

impl Display for Error {
  fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
    match self {
      Error::Empty => write!(f, "Queue is empty"),
    }
  }
}

impl std::error::Error for Error {}
