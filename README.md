# Verified Sieve

Implementing [Sieve of Eratosthenes](https://en.wikipedia.org/wiki/Sieve_of_Eratosthenes) to learn [Dafny](https://dafny.org/).

## Goal

Implement a `method Eratosthenes(n: int) returns (primes: array<int>)` which computes an array of primes up to `n`.
Dafny postconditions should be used to ensure that the output array satisfies the following properties:
* is strictly increasing, and therefore contains no duplicates.
* contains only primes.
* contains *every* prime in the desired interval `[2, n)`.

## Status

Done! Pending 1st discussion with teammates.