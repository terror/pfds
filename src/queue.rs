use super::*;

#[derive(Debug, Clone, PartialEq)]
pub enum QueueError {
  Empty,
}

impl Display for QueueError {
  fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
    match self {
      QueueError::Empty => write!(f, "Queue is empty"),
    }
  }
}

impl std::error::Error for QueueError {}

pub trait Queue<'a, T: Clone + Send + Sync + 'a> {
  /// Removes and returns a new queue without the front element.
  fn dequeue(self) -> Result<Self, QueueError>
  where
    Self: Sized;

  /// Creates an empty queue.
  fn empty() -> Self;

  /// Adds an element to the rear of the queue.
  fn enqueue(self, x: T) -> Self;

  /// Returns the front element of the queue without removing it.
  ///
  /// Returns `QueueError::Empty` if the queue is empty.
  fn head(&self) -> Result<T, QueueError>;

  /// Returns true if the queue contains no elements.
  fn is_empty(&self) -> bool;
}

/// A purely functional queue implementation using the Banker's method.
///
/// This implementation maintains two streams:
/// - `front`: Front stream for efficient head/tail operations
/// - `rear`: Rear stream for efficient enqueue operations
///
/// The key invariant is that `len_rear ≤ len_front`, which ensures that
/// operations remain efficient by automatically rebalancing when
/// the rear becomes longer than the front.
///
/// # Examples
/// ```
/// use pfds::{BankersQueue, Queue};
///
/// let mut q = BankersQueue::empty();
/// q = q.enqueue(1).enqueue(2).enqueue(3);
///
/// assert_eq!(q.head().unwrap(), 1);
/// q = q.dequeue().unwrap();
/// assert_eq!(q.head().unwrap(), 2);
/// ```
#[derive(Clone, Debug, PartialEq)]
pub struct BankersQueue<'a, T: Clone + Send + Sync + 'a> {
  front: Stream<'a, T>,
  len_front: usize,
  rear: Stream<'a, T>,
  len_rear: usize,
}

impl<'a, T: Clone + Send + Sync + 'a> Queue<'a, T> for BankersQueue<'a, T> {
  /// Removes the front element and returns a new queue.
  ///
  /// This operation is O(1) amortized. It removes the head of the front stream
  /// and may trigger rebalancing to maintain the invariant.
  ///
  /// # Examples
  /// ```
  /// use pfds::{BankersQueue, Queue};
  /// let q = BankersQueue::empty().enqueue(1).enqueue(2);
  /// let q = q.dequeue().unwrap();
  /// assert_eq!(q.head().unwrap(), 2);
  /// ```
  fn dequeue(self) -> Result<Self, QueueError> {
    match self.front.tail() {
      Some(front_tail) => Ok(Self::queue(
        front_tail,
        self.len_front - 1,
        self.rear,
        self.len_rear,
      )),
      None => Err(QueueError::Empty),
    }
  }

  /// Creates a new empty queue.
  ///
  /// # Examples
  /// ```
  /// use pfds::{BankersQueue, Queue};
  /// let q: BankersQueue<i32> = BankersQueue::empty();
  /// assert!(q.is_empty());
  /// ```
  fn empty() -> Self {
    BankersQueue {
      front: Stream::nil(),
      len_front: 0,
      rear: Stream::nil(),
      len_rear: 0,
    }
  }

  /// Adds an element to the rear of the queue.
  ///
  /// This operation is O(1) amortized. The element is added to the rear stream,
  /// and rebalancing occurs automatically when the invariant is violated.
  ///
  /// # Examples
  /// ```
  /// use pfds::{BankersQueue, Queue};
  /// let q = BankersQueue::empty().enqueue(1).enqueue(2);
  /// assert_eq!(q.head().unwrap(), 1); // FIFO order
  /// ```
  fn enqueue(self, x: T) -> Self {
    Self::queue(
      self.front,
      self.len_front,
      Stream::cons(x, self.rear),
      self.len_rear + 1,
    )
  }

  /// Returns the front element of the queue without removing it.
  ///
  /// This operation is O(1) since we can directly access the head of the front stream.
  ///
  /// # Examples
  /// ```
  /// use pfds::{BankersQueue, Queue};
  /// let q = BankersQueue::empty().enqueue(42);
  /// assert_eq!(q.head().unwrap(), 42);
  ///
  /// let empty: BankersQueue<i32> = BankersQueue::empty();
  /// assert!(empty.head().is_err());
  /// ```
  fn head(&self) -> Result<T, QueueError> {
    match self.front.head() {
      Some(head) => Ok(head),
      None => Err(QueueError::Empty),
    }
  }

  /// Returns true if the queue contains no elements.
  ///
  /// This operation is O(1) since we track the front length.
  ///
  /// # Examples
  /// ```
  /// use pfds::{BankersQueue, Queue};
  /// let q: BankersQueue<i32> = BankersQueue::empty();
  /// assert!(q.is_empty());
  ///
  /// let q = q.enqueue(42);
  /// assert!(!q.is_empty());
  /// ```
  fn is_empty(&self) -> bool {
    self.len_front == 0
  }
}

impl<'a, T: Clone + Send + Sync + 'a> BankersQueue<'a, T> {
  /// Internal constructor that maintains the queue invariant.
  ///
  /// Ensures that `len_rear ≤ len_front` by rebalancing when necessary.
  ///
  /// When rebalancing occurs, the rear stream is reversed and appended
  /// to the front stream, and the rear is reset to empty.
  fn queue(
    front: Stream<'a, T>,
    len_front: usize,
    rear: Stream<'a, T>,
    len_rear: usize,
  ) -> Self {
    if len_rear <= len_front {
      BankersQueue {
        front,
        len_front,
        rear,
        len_rear,
      }
    } else {
      BankersQueue {
        front: front.append(rear.reverse()),
        len_front: len_front + len_rear,
        rear: Stream::nil(),
        len_rear: 0,
      }
    }
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn empty_queue() {
    let queue = BankersQueue::<i32>::empty();
    assert!(queue.is_empty());
    assert!(queue.head().is_err());
    assert!(queue.dequeue().is_err());
  }

  #[test]
  fn single_element() {
    let queue = BankersQueue::<i32>::empty().enqueue(42);
    assert_eq!(queue.head().unwrap(), 42);
    assert_eq!(queue.dequeue().unwrap(), BankersQueue::<i32>::empty());
  }

  #[test]
  fn multiple_elements() {
    let queue = BankersQueue::<i32>::empty()
      .enqueue(1)
      .enqueue(2)
      .enqueue(3);

    assert_eq!(queue.head().unwrap(), 1);

    let queue = queue.dequeue().unwrap();
    assert_eq!(queue.head().unwrap(), 2);

    let queue = queue.dequeue().unwrap();
    assert_eq!(queue.head().unwrap(), 3);

    let queue = queue.dequeue().unwrap();
    assert!(queue.is_empty());
  }

  #[test]
  fn rebalancing() {
    let mut queue = BankersQueue::<i32>::empty();

    for i in 1..=10 {
      queue = queue.enqueue(i);
    }

    for i in 1..=10 {
      assert_eq!(queue.head().unwrap(), i);
      queue = queue.dequeue().unwrap();
    }

    assert!(queue.is_empty());
  }

  #[test]
  fn invariants_maintained() {
    let mut queue = BankersQueue::<i32>::empty();

    for i in 1..=5 {
      queue = queue.enqueue(i);
      assert!(queue.len_rear <= queue.len_front);
    }
  }
}
