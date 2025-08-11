use super::*;

pub enum StreamCell<'a, T> {
  Nil,
  Cons(T, Stream<'a, T>),
}

#[derive(Clone)]
pub struct Stream<'a, T> {
  cell: Rc<dyn Fn() -> StreamCell<'a, T> + 'a>,
}

impl<'a, T: Clone + Debug + 'a> Debug for Stream<'a, T> {
  fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
    write!(f, "Stream({:?})", Into::<Vec<T>>::into(self.clone()))
  }
}

impl<'a, T: Clone + 'a> From<Vec<T>> for Stream<'a, T> {
  fn from(vec: Vec<T>) -> Self {
    vec
      .into_iter()
      .rev()
      .fold(Stream::nil(), |acc, x| Stream::cons(x, acc))
  }
}

impl<'a, T: Clone + PartialEq + 'a> PartialEq for Stream<'a, T> {
  fn eq(&self, other: &Self) -> bool {
    match (self.force(), other.force()) {
      (StreamCell::Nil, StreamCell::Nil) => true,
      (StreamCell::Cons(x1, tail1), StreamCell::Cons(x2, tail2)) => {
        x1 == x2 && tail1 == tail2
      }
      _ => false,
    }
  }
}

impl<'a, T: Clone + 'a> From<Stream<'a, T>> for Vec<T> {
  fn from(stream: Stream<'a, T>) -> Self {
    let mut result = Vec::new();

    let mut current = stream;

    loop {
      match current.force() {
        StreamCell::Nil => break,
        StreamCell::Cons(x, tail) => {
          result.push(x);
          current = tail;
        }
      }
    }

    result
  }
}

impl<'a, T: Clone + 'a> Stream<'a, T> {
  /// Appends another stream to the end of this stream.
  ///
  /// Returns a new stream containing all elements from this stream
  /// followed by all elements from the other stream.
  ///
  /// # Examples
  /// ```
  /// use pfds::Stream;
  /// let s1: Stream<i32> = vec![1, 2, 3].into();
  /// let s2: Stream<i32> = vec![4, 5, 6].into();
  /// let result = s1.append(s2);
  /// let vec: Vec<i32> = result.into();
  /// assert_eq!(vec, vec![1, 2, 3, 4, 5, 6]);
  /// ```
  pub fn append(self, other: Stream<'a, T>) -> Stream<'a, T> {
    Stream {
      cell: Rc::new(move || match self.force() {
        StreamCell::Nil => other.force(),
        StreamCell::Cons(x, tail) => {
          StreamCell::Cons(x, tail.append(other.clone()))
        }
      }),
    }
  }

  /// Constructs a new stream with the given head element and tail stream.
  ///
  /// This is the fundamental constructor for non-empty streams.
  ///
  /// # Examples
  /// ```
  /// use pfds::Stream;
  /// let stream = Stream::cons(1, Stream::cons(2, Stream::nil()));
  /// let vec: Vec<i32> = stream.into();
  /// assert_eq!(vec, vec![1, 2]);
  /// ```
  pub fn cons(head: T, tail: Stream<'a, T>) -> Stream<'a, T> {
    Stream {
      cell: Rc::new(move || StreamCell::Cons(head.clone(), tail.clone())),
    }
  }

  /// Drops the first n elements from the stream.
  ///
  /// Returns a new stream with the first n elements removed.
  /// If n is greater than the stream length, returns an empty stream.
  ///
  /// # Examples
  /// ```
  /// use pfds::Stream;
  /// let stream: Stream<i32> = vec![1, 2, 3, 4, 5].into();
  /// let result = stream.drop(2);
  /// let vec: Vec<i32> = result.into();
  /// assert_eq!(vec, vec![3, 4, 5]);
  /// ```
  pub fn drop(self, n: usize) -> Stream<'a, T> {
    fn drop_helper<'b, U: Clone + 'b>(
      n: usize,
      stream: Stream<'b, U>,
    ) -> StreamCell<'b, U> {
      if n == 0 {
        stream.force()
      } else {
        match stream.force() {
          StreamCell::Nil => StreamCell::Nil,
          StreamCell::Cons(_, tail) => drop_helper(n - 1, tail),
        }
      }
    }

    Stream {
      cell: Rc::new(move || drop_helper(n, self.clone())),
    }
  }

  /// Forces evaluation of the stream's suspended computation.
  ///
  /// This method evaluates the lazy computation stored in the stream
  /// and returns the resulting StreamCell.
  ///
  /// # Examples
  /// ```
  /// use pfds::{Stream, StreamCell};
  /// let stream: Stream<i32> = Stream::nil();
  /// assert!(matches!(stream.force(), StreamCell::Nil));
  /// ```
  pub fn force(&self) -> StreamCell<'a, T> {
    (self.cell)()
  }

  /// Returns the first element of the stream, if it exists.
  ///
  /// Returns None for empty streams, Some(element) for non-empty streams.
  ///
  /// # Examples
  /// ```
  /// use pfds::Stream;
  /// let stream = Stream::cons(42, Stream::nil());
  /// assert_eq!(stream.head(), Some(42));
  ///
  /// let empty: Stream<i32> = Stream::nil();
  /// assert_eq!(empty.head(), None);
  /// ```
  pub fn head(&self) -> Option<T> {
    match self.force() {
      StreamCell::Nil => None,
      StreamCell::Cons(x, _) => Some(x),
    }
  }

  /// Returns true if the stream is empty, false otherwise.
  ///
  /// # Examples
  /// ```
  /// use pfds::Stream;
  /// let empty: Stream<i32> = Stream::nil();
  /// assert!(empty.is_empty());
  ///
  /// let non_empty = Stream::cons(1, Stream::nil());
  /// assert!(!non_empty.is_empty());
  /// ```
  pub fn is_empty(&self) -> bool {
    matches!(self.force(), StreamCell::Nil)
  }

  /// Constructs an empty stream.
  ///
  /// This is the base case for stream construction, representing
  /// a stream with no elements.
  ///
  /// # Examples
  /// ```
  /// use pfds::Stream;
  /// let empty: Stream<i32> = Stream::nil();
  /// assert!(empty.is_empty());
  /// ```
  pub fn nil() -> Stream<'a, T> {
    Stream {
      cell: Rc::new(|| StreamCell::Nil),
    }
  }

  /// Reverses the stream.
  ///
  /// Returns a new stream with all elements in reverse order.
  ///
  /// # Examples
  /// ```
  /// use pfds::Stream;
  /// let stream: Stream<i32> = vec![1, 2, 3, 4, 5].into();
  /// let result = stream.reverse();
  /// let vec: Vec<i32> = result.into();
  /// assert_eq!(vec, vec![5, 4, 3, 2, 1]);
  /// ```
  pub fn reverse(self) -> Stream<'a, T> {
    fn reverse_helper<'b, U: Clone + 'b>(
      stream: Stream<'b, U>,
      acc: Stream<'b, U>,
    ) -> StreamCell<'b, U> {
      match stream.force() {
        StreamCell::Nil => acc.force(),
        StreamCell::Cons(x, tail) => reverse_helper(tail, Stream::cons(x, acc)),
      }
    }

    Stream {
      cell: Rc::new(move || reverse_helper(self.clone(), Stream::nil())),
    }
  }

  /// Returns the tail of the stream (all elements except the first).
  ///
  /// Returns None for empty streams, Some(tail_stream) for non-empty streams.
  ///
  /// # Examples
  /// ```
  /// use pfds::Stream;
  /// let stream = Stream::cons(1, Stream::cons(2, Stream::nil()));
  /// let tail = stream.tail().unwrap();
  /// let vec: Vec<i32> = tail.into();
  /// assert_eq!(vec, vec![2]);
  /// ```
  pub fn tail(&self) -> Option<Stream<'a, T>> {
    match self.force() {
      StreamCell::Nil => None,
      StreamCell::Cons(_, tail) => Some(tail),
    }
  }

  /// Takes the first n elements from the stream.
  ///
  /// Returns a new stream containing at most the first n elements.
  /// If n is greater than the stream length, returns the entire stream.
  ///
  /// # Examples
  /// ```
  /// use pfds::Stream;
  /// let stream: Stream<i32> = vec![1, 2, 3, 4, 5].into();
  /// let result = stream.take(3);
  /// let vec: Vec<i32> = result.into();
  /// assert_eq!(vec, vec![1, 2, 3]);
  /// ```
  pub fn take(self, n: usize) -> Stream<'a, T> {
    Stream {
      cell: Rc::new(move || {
        if n == 0 {
          StreamCell::Nil
        } else {
          match self.force() {
            StreamCell::Nil => StreamCell::Nil,
            StreamCell::Cons(x, tail) => StreamCell::Cons(x, tail.take(n - 1)),
          }
        }
      }),
    }
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn append() {
    assert_eq!(
      Stream::<i32>::from(vec![1, 2, 3]).append(vec![4, 5, 6].into()),
      vec![1, 2, 3, 4, 5, 6].into()
    );
  }

  #[test]
  fn append_empty() {
    assert_eq!(
      Stream::<i32>::nil().append(vec![1, 2, 3].into()),
      vec![1, 2, 3].into()
    );
  }

  #[test]
  fn cons() {
    assert_eq!(
      Stream::cons(1, Stream::cons(2, Stream::cons(3, Stream::nil()))),
      vec![1, 2, 3].into()
    );
  }

  #[test]
  fn drop() {
    assert_eq!(
      Stream::<i32>::from(vec![1, 2, 3, 4, 5]).drop(2),
      vec![3, 4, 5].into()
    );
  }

  #[test]
  fn drop_more_than_length() {
    assert_eq!(Stream::<i32>::from(vec![1, 2]).drop(5), Stream::nil());
  }

  #[test]
  fn drop_zero() {
    assert_eq!(
      Stream::<i32>::from(vec![1, 2, 3]).drop(0),
      vec![1, 2, 3].into()
    );
  }

  #[test]
  fn nil() {
    assert_eq!(Stream::<i32>::nil(), Stream::nil());
  }

  #[test]
  fn reverse() {
    assert_eq!(
      Stream::<i32>::from(vec![1, 2, 3, 4, 5]).reverse(),
      vec![5, 4, 3, 2, 1].into()
    );
  }

  #[test]
  fn reverse_empty() {
    assert_eq!(Stream::<i32>::nil().reverse(), Stream::nil());
  }

  #[test]
  fn reverse_single() {
    assert_eq!(Stream::cons(42, Stream::nil()).reverse(), vec![42].into());
  }

  #[test]
  fn take() {
    assert_eq!(
      Stream::<i32>::from(vec![1, 2, 3, 4, 5]).take(3),
      vec![1, 2, 3].into()
    );
  }

  #[test]
  fn take_more_than_length() {
    assert_eq!(Stream::<i32>::from(vec![1, 2]).take(5), vec![1, 2].into());
  }

  #[test]
  fn take_zero() {
    assert_eq!(Stream::<i32>::from(vec![1, 2, 3]).take(0), Stream::nil());
  }
}
