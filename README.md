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

Here are some initial observations in the meantime:
* The implementation is quite inefficient, as Dafny does not offer dynamic arrays.
To work around this issue, our code currently makes many extraneous copies on arrays.
* Proving existentials is surprisingly simple for Dafny.
For example, the following works just fine:
```
lemma TestComposite()
    ensures !IsPrime(361)
{
    var p := 19;
    var x := 361;
    var y := 361 % 19;
    assert y == 0;
}
```
* To prove "for all" properties over an integer interval (such as `ensures forall x :: m <= x < n ==> !IsPrime(x)`),
currently we resort to induction, which is encoded in Dafny as recursions.
This looks quite clunky and maybe there are better ways.
* While Dafny array doesn't seem to offer "basic" functionalities such as membership-checking or filtering,
implementing desired functionalities from scratch turned out to be less involved than expected.
