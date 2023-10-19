//! Library functions

use std::{
    collections::{HashSet, VecDeque},
    fmt::{self, Write},
    mem,
    sync::{PoisonError, RwLock},
};

/// Detect if a number is prime.
///
/// ```
/// use prime_combination_connections::is_prime;
/// assert!(is_prime(7));
/// assert!(is_prime(37));
/// assert!(!is_prime(91));
/// assert!(!is_prime(9_912));
/// assert!(!is_prime(92_579));
/// assert!(!is_prime(1_000_000));
/// assert!(!is_prime(1_000_000));
/// assert!(is_prime(6_700_417));
/// ```
pub fn is_prime(p: usize) -> bool {
    /// Cache of everything we've computed so far.
    static PRIME_VEC: RwLock<Vec<bool>> = RwLock::new(Vec::new());

    // Check if we've computed for the given value.
    let primes = PRIME_VEC.read().unwrap_or_else(PoisonError::into_inner);
    if primes.len() > p {
        // If we have, then we can return it.
        primes[p]
    } else {
        // Release the read lock so we can write more values to the vector.
        mem::drop(primes);
        // If we haven't computed it, then use a modified Sieve of Eratosthenes to detect.
        let mut primes_mut = PRIME_VEC.write().unwrap_or_else(PoisonError::into_inner);
        // If someone else extended it while we were waiting, we can just return their value.
        if primes_mut.len() > p {
            return primes_mut[p];
        }
        if primes_mut.is_empty() {
            // Initialize with 0-5: Indicate that 2, 3, and 5 are all prime
            primes_mut.extend_from_slice(&[false, false, true, true, false, true]);
        }
        let start_idx = primes_mut.len();
        primes_mut.extend(
            // Chunks of length 6: only values congruent to 1 or 5 modulo 6 can be prime.
            //
            // Let's already mark other values as composite, save having to sweep 2s and 3s.
            std::iter::repeat([false, true, false, false, false, true])
                .take(p.saturating_sub(start_idx) / 6 + 1)
                .flat_map(IntoIterator::into_iter),
        );
        // Some debug assertions for testing that the extension goes correctly.
        #[cfg(debug_assertions)]
        if p >= 6 {
            assert!(primes_mut.len() > p, "Extended chunk is too short");
            assert!(
                primes_mut.len() <= p + 6,
                "Extended chunk is too long: for p {p}, length became {}",
                primes_mut.len()
            );
        }
        // Sweep all primes >3, since 2 and 3 are already handled by the initialization pattern
        // above.
        for i in 5..primes_mut.len() {
            if !primes_mut[i] {
                // `i` wasn't a prime
                continue;
            }
            if i * i > primes_mut.len() {
                // i > sqrt(p), so we know whether all numbers <= p are primes.
                break;
            }
            // Start sweeping at either i^2 or the first multiple of i in the new block of nubmers,
            // whichever is smaller.
            //
            // This saves us from re-tagging values which must have been tagged by a smaller prime
            // number. We miss if `start_idx` is a multiple of `i`, but a `false` already gets
            // inserted there.
            let sweep_start = (i * i).max(start_idx - (start_idx % i) + i);
            for j in (sweep_start..primes_mut.len()).step_by(i) {
                primes_mut[j] = false;
            }
        }
        primes_mut[p]
    }
}

/// A number written out in base `RADIX`, with length `LENGTH`
#[derive(Copy, Clone, PartialEq, Eq, Hash)]
pub struct Number<const LENGTH: usize, const RADIX: usize> {
    /// The digits from most to least significant.
    digits: [u8; LENGTH],
}
/// Convert from a numerical value.
impl<const LENGTH: usize, const RADIX: usize> From<usize> for Number<LENGTH, RADIX> {
    fn from(mut value: usize) -> Self {
        let mut digits = [0; LENGTH];
        for digit in digits.iter_mut().rev() {
            *digit = (value % RADIX) as u8;
            value /= RADIX;
        }
        Self { digits }
    }
}
/// Convert to a numerical value.
impl<const LENGTH: usize, const RADIX: usize> From<Number<LENGTH, RADIX>> for usize {
    fn from(value: Number<LENGTH, RADIX>) -> Self {
        let mut acc = 0;
        for digit in value.digits {
            acc = acc * RADIX + digit as usize;
        }
        acc
    }
}
impl<const LENGTH: usize, const RADIX: usize> Number<LENGTH, RADIX> {
    /// Get if this number is prime.
    pub fn is_prime(self) -> bool {
        is_prime(usize::from(self))
    }

    /// Get the value by decrementing at the given digit.
    ///
    /// Note that this indexes starting at the most significant digit, so (if we don't wrap), this
    /// is equivalent to subtracting `RADIX ** (LENGTH-1-digit)` from `self`.
    ///
    /// ```
    /// use prime_combination_connections::Number;
    /// assert_eq!(Number::<5, 10>::from(13).decrement_digit(3), Number::from(3));
    /// assert_eq!(Number::<5, 10>::from(13).decrement_digit(1), Number::from(9013));
    /// ```
    pub fn decrement_digit(mut self, digit: usize) -> Self {
        let new_digit = self.digits[digit].checked_sub(1).unwrap_or(RADIX as u8 - 1);
        self.digits[digit] = new_digit;
        self
    }

    /// Get the value by incrementing at the given digit.
    ///
    /// Note that this indexes starting at the most significant digit, so (if we don't wrap), this
    /// is equivalent to adding `RADIX ** (LENGTH-1-digit)` to `self`.
    ///
    /// ```
    /// use prime_combination_connections::Number;
    /// assert_eq!(Number::<5, 10>::from(3).increment_digit(3), Number::from(13));
    /// assert_eq!(Number::<5, 10>::from(9013).increment_digit(1), Number::from(13));
    /// ```
    pub fn increment_digit(mut self, digit: usize) -> Self {
        let new_digit = (self.digits[digit] + 1) % (RADIX as u8);
        self.digits[digit] = new_digit;
        self
    }

    /// Get all neighboring digits.
    pub fn neighbors(self) -> impl Iterator<Item = Self> {
        (0..LENGTH).flat_map(move |digit| {
            let down = self.decrement_digit(digit);
            let up = self.increment_digit(digit);
            [down, up].into_iter()
        })
    }

    /// Get all neighboring digits which are prime.
    ///
    /// ```
    /// use prime_combination_connections::Number;
    /// use std::collections::HashSet;
    /// let seed = Number::<5, 10>::from(92479);
    /// assert_eq!(
    ///     seed.neighboring_primes().collect::<HashSet<_>>(),
    ///     HashSet::from_iter([Number::from(93479), Number::from(92489)]),
    /// );
    /// ```
    pub fn neighboring_primes(self) -> impl Iterator<Item = Self> {
        self.neighbors().filter(|number| number.is_prime())
    }

    /// Get the extent of the connected component rooted at `self`.
    ///
    /// ```
    /// use prime_combination_connections::Number;
    /// let seed = Number::<5, 10>::from(92479);
    /// assert_eq!(
    ///     seed.connected_component(),
    ///     std::collections::HashSet::from_iter([seed, Number::from(93479), Number::from(92489)]),
    /// );
    /// ```
    pub fn connected_component(self) -> HashSet<Self> {
        let mut visited = HashSet::new();
        let mut queued = VecDeque::from_iter([self]);
        while let Some(value) = queued.pop_front() {
            visited.insert(value);
            queued.extend(value.neighboring_primes().filter(|p| !visited.contains(p)));
        }
        visited
    }

    /// Get the path from one value to another, only going through primes.
    ///
    /// If no such path exists, then it returns `None`.
    pub fn path_to(self, other: Self) -> Option<Vec<Self>> {
        use pathfinding::directed::bfs;
        bfs::bfs(
            &self,
            |node| node.neighboring_primes(),
            |node| *node == other,
        )
    }
}
impl<const LENGTH: usize, const RADIX: usize> fmt::Debug for Number<LENGTH, RADIX> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for digit in self.digits {
            f.write_char(char::from_digit(digit as u32, RADIX as u32).unwrap())?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_prime_count() {
        assert_eq!((0..1000).filter(|n| is_prime(*n)).count(), 168,);
        assert_eq!((0..10000).filter(|n| is_prime(*n)).count(), 1229,);
        assert_eq!((0..100000).filter(|n| is_prime(*n)).count(), 9592,);
    }

    #[test]
    fn test_number_round_trip() {
        #[track_caller]
        fn test_for_length_radix<const LENGTH: usize, const RADIX: usize>() {
            for value in 0..RADIX.pow(LENGTH as u32) {
                assert_eq!(
                    value,
                    Number::<LENGTH, RADIX>::from(value).into(),
                    "Round-trip mismatch for value {value} with radix {RADIX}, length {LENGTH}",
                );
                assert_eq!(
                    is_prime(value),
                    Number::<LENGTH, RADIX>::from(value).is_prime(),
                    "Primality mismatch for value {value} with radix {RADIX}, length {LENGTH}",
                );
            }
        }
        test_for_length_radix::<5, 10>();
    }

    /// Test my code against the one solution in
    /// <https://incoherency.co.uk/blog/stories/prime-combination-solution.html>
    #[test]
    fn test_against_james_stanley() {
        // This is our starting value.
        let seed = Number::<5, 10>::from(1);
        // Generate the connected component.
        let component = seed.connected_component();
        eprintln!("{component:?}");
        // Assert every step along the way is in our connected component.
        assert!(component.contains(&Number::from(1)));
        assert!(component.contains(&Number::from(2)));
        assert!(component.contains(&Number::from(3)));
        assert!(component.contains(&Number::from(13)));
        assert!(component.contains(&Number::from(9013)));
        assert!(component.contains(&Number::from(99013)));
        assert!(component.contains(&Number::from(99023)));
        assert!(component.contains(&Number::from(99923)));
        assert!(component.contains(&Number::from(99823)));
        assert!(component.contains(&Number::from(99833)));
        assert!(component.contains(&Number::from(9833)));
        assert!(component.contains(&Number::from(9733)));
        assert!(component.contains(&Number::from(733)));
        assert!(component.contains(&Number::from(10733)));
        assert!(component.contains(&Number::from(10723)));
        // Assert we find the same path:
        assert_eq!(
            seed.path_to(Number::from(10723))
                .expect("Couldn't find a path"),
            vec![
                00001.into(),
                00002.into(),
                00003.into(),
                00013.into(),
                09013.into(),
                99013.into(),
                99023.into(),
                99923.into(),
                99823.into(),
                99833.into(),
                09833.into(),
                09733.into(),
                00733.into(),
                10733.into(),
                10723.into(),
            ]
        );
    }
}
