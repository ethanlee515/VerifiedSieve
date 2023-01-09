include "libraries/src/NonlinearArithmetic/DivMod.dfy"
include "libraries/src/NonlinearArithmetic/Mul.dfy"

import opened DivMod
import opened Mul

/* -- Integer array operations -- */

// Checks what the name suggests
predicate Contains(xs: array<int>, x: int)
reads xs
{
    exists i :: 0 <= i < xs.Length && xs[i] == x
}

// Checks what the name suggests
// Implies uniqueness
predicate StrictlyIncreasing(xs: array<int>)
reads xs
{
    forall i, j :: 0 <= i < j < xs.Length ==> xs[i] < xs[j]
}

// Appends an integer x to the end of an array xs.
method Append(xs: array<int>, x: int) returns (ys: array<int>)
ensures ys.Length == xs.Length + 1
ensures forall j :: 0 <= j < xs.Length ==> xs[j] == ys[j]
ensures ys[xs.Length] == x
ensures forall e :: Contains(ys, e) <==> (Contains(xs, e) || e == x)
{
    ys := new int[xs.Length + 1](i => 0);
    var j := 0;
    while(j < xs.Length)
    invariant forall k :: 0 <= k < j ==> k < xs.Length && ys[k] == xs[k]
    {
        ys[j] := xs[j];
        j := j + 1;
    }
    ys[xs.Length] := x;
}

// Creates an array containing integers in the interval [low, high)
method Range(low: int, high: int) returns (arr: array<int>)
requires high - low >= 0
ensures arr.Length == high - low
ensures forall i :: 0 <= i < high - low ==> arr[i] == low + i
ensures forall x :: Contains(arr, x) <==> low <= x < high
ensures StrictlyIncreasing(arr)
{
    var len := high - low;
    arr := new int[len](i => 0);
    var i := 0;
    while(i < len)
    invariant forall j :: 0 <= j < i ==> j < arr.Length && arr[j] == j + low
    {
        arr[i] := i + low;
        i := i + 1;
    }
    assert forall x :: low <= x < high ==> 0 <= x - low < arr.Length;
}

/* -- prime numbers properties -- */

// Checks if an integer is prime.
predicate IsPrime(x: int)
{
    x >= 2 && forall y :: 2 <= y < x ==> x % y != 0
}

lemma PrimeDivisorExists(n: int)
decreases n
requires n >= 2
ensures exists p :: IsPrime(p) && n % p == 0
{
    if(!IsPrime(n)) {
        var m :| 2 <= m < n && n % m == 0;
        PrimeDivisorExists(m);
        var p :| IsPrime(p) && m % p == 0;
        LemmaFundamentalDivMod(n, m);
        LemmaMulModNoopLeft(m, n / m, p);
        LemmaSmallMod(0, p);
    }
}

/* -- spec and properties of intermediate results -- */

predicate SievedUpTo(xs: array<int>, m: int, n: int)
reads xs
{
    forall x :: Contains(xs, x) <==> (2 <= x < n && (forall p :: IsPrime(p) && 2 <= p < m ==> x % p != 0))
}

lemma SievedUpTo_lb(xs: array<int>, m: int, n: int)
requires SievedUpTo(xs, m, n)
requires xs.Length > 0
ensures xs[0] >= m
{
    var x := xs[0];
    assert Contains(xs, x);
    if (x < m) {
        PrimeDivisorExists(x);
        var p :| IsPrime(p) && x % p == 0;
        if(p >= m) {
            LemmaSmallMod(x, p);
        }
    }
}

lemma SievedHeadIsPrime(xs: array<int>, m: int, n: int)
requires SievedUpTo(xs, m, n)
requires StrictlyIncreasing(xs)
requires xs.Length > 0
ensures IsPrime(xs[0])
{
    var x := xs[0];
    if(!IsPrime(x)) {
        assert Contains(xs, x);
        assert x >= 2;
        PrimeDivisorExists(x);
        var m :| IsPrime(m) && x % m == 0;
        if(m > x) {
            LemmaSmallMod(x, m);
        }
        assert Contains(xs, x);
        assert Contains(xs, m);
    }
}

lemma NoPrimesBeforeSievedHeadAux(xs: array<int>, m: int, n: int, i: int)
decreases i
requires m >= 0
requires SievedUpTo(xs, m, n)
requires StrictlyIncreasing(xs)
requires xs.Length > 0
requires m <= i <= xs[0]
ensures forall c :: m <= c < i ==> !IsPrime(c)
{
    if(m + 1 <= i - 1) {
        NoPrimesBeforeSievedHeadAux(xs, m, n, i - 1);
    }
    if(!Contains(xs, i - 1)) {
        assert Contains(xs, xs[0]);
    }
}

lemma NoPrimesBeforeSievedHead(xs: array<int>, m: int, n: int)
requires SievedUpTo(xs, m, n)
requires StrictlyIncreasing(xs)
requires xs.Length > 0
requires m >= 0
ensures forall c :: m <= c < xs[0] ==> !IsPrime(c)
{
    SievedUpTo_lb(xs, m, n);
    NoPrimesBeforeSievedHeadAux(xs, m, n, xs[0]);
}

lemma SievedTailIsCompositeAux(xs: array<int>, m: int, n: int, y: int)
requires xs.Length == 0
requires SievedUpTo(xs, m, n)
requires 0 <= m < y <= n
ensures forall x :: m <= x < y ==> !IsPrime(x)
{
    if(m + 1 != y) {
        SievedTailIsCompositeAux(xs, m, n, y - 1);
    }
    assert !Contains(xs, y - 1);
}

lemma SievedTailIsComposite(xs: array<int>, m: int, n: int)
requires xs.Length == 0
requires SievedUpTo(xs, m, n)
requires 0 <= m
ensures forall x :: m <= x < n ==> !IsPrime(x)
{
    if(m < n) {
        SievedTailIsCompositeAux(xs, m, n, n);
    }
}

/* -- actual program -- */

// Identify a prime and filter away its multiples
method SieveNext(xs: array<int>, n: int) returns (sieved: array<int>)
requires xs.Length > 0
// updates the `SievedUpTo` property appropriately
requires SievedUpTo(xs, xs[0], n)
ensures SievedUpTo(sieved, xs[0] + 1, n)
// preserves strictly-increasing
requires StrictlyIncreasing(xs)
ensures StrictlyIncreasing(sieved)
// for proving termination, when this is called iteratively
ensures sieved.Length < xs.Length
{
    var x := xs[0];
    SievedHeadIsPrime(xs, x, n);
    sieved := new int[0];
    var i := 0;
    while(i < xs.Length)
    invariant i <= xs.Length
    // `sieved` contains "the right things" so far.
    invariant forall e :: Contains(sieved, e) <==> exists j :: 0 <= j < i && xs[j] == e && e % x != 0
    // `sieved` is increasing.
    invariant i < xs.Length && sieved.Length > 0 ==> sieved[sieved.Length - 1] < xs[i]
    invariant StrictlyIncreasing(sieved)
    // sieving decreases the length of the array
    invariant i == 0 ==> sieved.Length == 0
    invariant i > 0 ==> sieved.Length < i
    {
        if(xs[i] % x != 0) {
            sieved := Append(sieved, xs[i]);
        }
        i := i + 1;
    }
    assert forall e :: Contains(sieved, e) <==> (Contains(xs, e) && e % x != 0);
}

// Computes an array of primes up to n
method Eratosthenes(n: int) returns (primes: array<int>)
requires n > 2
ensures forall m :: (2 <= m < n && IsPrime(m)) ==> Contains(primes, m)
ensures StrictlyIncreasing(primes)
{
    primes := new int[0];
    var xs := Range(2, n);
    while(xs.Length > 0)
    // closed form for intermediate results of the sieve
    invariant xs.Length > 0 ==> SievedUpTo(xs, xs[0], n)
    invariant StrictlyIncreasing(xs)
    // the prime list indeed contains only primes
    invariant forall p :: Contains(primes, p) ==> IsPrime(p)
    // the prime list hasn't "missed" anything so far
    invariant xs.Length > 0 ==> forall m :: 2 <= m < xs[0] && IsPrime(m) ==> Contains(primes, m)
    // what we get in the final iteration
    invariant xs.Length == 0 ==> forall m :: 2 <= m < n && IsPrime(m) ==> Contains(primes, m)
    // primes are added in increasing order
    invariant primes.Length > 0 && xs.Length > 0 ==> primes[primes.Length - 1] < xs[0]
    invariant StrictlyIncreasing(primes)
    {
        var p := xs[0];
        SievedHeadIsPrime(xs, p, n);
        xs := SieveNext(xs, n);
        if(xs.Length > 0) {
            SievedUpTo_lb(xs, p + 1, n);
            NoPrimesBeforeSievedHead(xs, p + 1, n);
        } else {
            SievedTailIsComposite(xs, p + 1, n);
        }
        primes := Append(primes, p);
    }
}

method PrintArr(xs: array<int>) {
    var i := 0;
    while(i < xs.Length) {
        print xs[i];
        print "\n";
        i := i + 1;
    }
}

method Main() {
    var primes := Eratosthenes(200);
    PrintArr(primes);
}