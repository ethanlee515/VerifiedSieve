# Verified Sieve

Implementing [Sieve of Eratosthenes](https://en.wikipedia.org/wiki/Sieve_of_Eratosthenes) to learn [Dafny](https://dafny.org/).

## Goal

Implement a method `primesUpTo(n)` which outputs an array of primes up to `n`.
Dafny postconditions should be used to ensure that the output array satisfies the following properties:
* contains only primes
* is non-decreasing
* contains no duplicates
* contains *every* prime in the desired interval
