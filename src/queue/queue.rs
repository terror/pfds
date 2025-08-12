use super::*;

pub trait Queue<'a, T: Clone + Send + Sync + 'a>: Iterator<Item = T> {
  /// Removes and returns a new queue without the front element.
  fn dequeue(self) -> Result<Self, Error>
  where
    Self: Sized;

  /// Creates an empty queue.
  fn empty() -> Self;

  /// Adds an element to the rear of the queue.
  fn enqueue(self, x: T) -> Self;

  /// Returns the front element of the queue without removing it.
  fn head(&self) -> Result<T, Error>;

  /// Returns true if the queue contains no elements.
  fn is_empty(&self) -> bool;
}
