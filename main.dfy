include "libraries/src/NonlinearArithmetic/DivMod.dfy"
include "libraries/src/NonlinearArithmetic/Mul.dfy"

import opened DivMod
import opened Mul

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

predicate SievedUpTo(xs: array<int>, p: int, n: int)
requires IsPrime(p)
reads xs
{
    forall x :: Contains(xs, x) <==> (2 <= x <= n && (forall y :: IsPrime(y) && 2 <= y <= p ==> x % y != 0))
}

lemma SievedHeadIsPrime(xs: array<int>, p: int, n: int)
requires IsPrime(p)
requires SievedUpTo(xs, p, n)
requires StrictlyIncreasing(xs)
requires xs.Length > 0
requires xs[0] >= 2
ensures IsPrime(xs[0])
{
    var x := xs[0];
    if(!IsPrime(x)) {
        PrimeDivisorExists(x);
        var m :| IsPrime(m) && x % m == 0;
        if(m > x) {
            LemmaSmallMod(x, m);
        }
        assert Contains(xs, x);
        assert Contains(xs, m);
    }
}

lemma NoPrimesBeforeSievedHeadAux(xs: array<int>, p: int, n: int, i: int)
decreases i
requires IsPrime(p)
requires SievedUpTo(xs, p, n)
requires StrictlyIncreasing(xs)
requires xs.Length > 0
requires xs[0] >= 2
requires p <= i <= xs[0]
ensures forall c :: p < c < i ==> !IsPrime(c)
{
    if(i == p) {

    } else {
        assert i > p;
        NoPrimesBeforeSievedHeadAux(xs, p, n, i - 1); 
        if(Contains(xs, i - 1)) {

        } else {
            assert Contains(xs, xs[0]);
        }
    }
}

lemma NoPrimesBeforeSievedHead(xs: array<int>, p: int, n: int)
requires IsPrime(p)
requires SievedUpTo(xs, p, n)
requires StrictlyIncreasing(xs)
requires xs.Length > 0
requires 2 <= p <= xs[0]
ensures forall c :: p < c < xs[0] ==> !IsPrime(c)
{
    NoPrimesBeforeSievedHeadAux(xs, p, n, xs[0]);
}

// Removes the i-th element of an array.
method RemoveIth(xs: array<int>, i: int) returns (ys: array<int>)
requires xs.Length >= 1
requires 0 <= i < xs.Length
ensures ys.Length == xs.Length - 1
ensures forall k :: 0 <= k < i ==> xs[k] == ys[k]
ensures forall k :: i + 1 <= k < xs.Length ==> xs[k] == ys[k - 1]
ensures forall k :: (0 <= k < xs.Length && k != i) ==> Contains(ys, xs[k])
{
    ys := new int[xs.Length - 1](i => 0);
    // Copying first part of xs into ys
    var j := 0;
    while(j < i)
    invariant forall k :: 0 <= k < j ==> k < ys.Length && ys[k] == xs[k]
    {
        ys[j] := xs[j];
        j := j + 1;
    }
    // Copying second part of xs into ys
    j := i + 1;
    while(j < xs.Length)
    invariant forall k :: 0 <= k < i ==> ys[k] == xs[k]
    invariant forall k :: i + 1 <= k < j ==> k - 1 < ys.Length && ys[k - 1] == xs[k]
    {
        ys[j - 1] := xs[j];
        j := j + 1;
    }
}

// Appends an integer x to the end of an array xs.
method Append(xs: array<int>, x: int) returns (ys: array<int>)
ensures ys.Length == xs.Length + 1
ensures forall j :: 0 <= j < xs.Length ==> xs[j] == ys[j]
ensures ys[xs.Length] == x
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

// TODO SievedUpto subset relationship on p??

method SieveNext(xs: array<int>, p: int, n: int) returns (sieved: array<int>)
requires IsPrime(p)
requires SievedUpTo(xs, p, n)
requires StrictlyIncreasing(xs)
requires xs.Length > 0
requires 2 <= p <= xs[0]
//ensures SievedUpTo(sieved, xs[0], n)
{
    SievedHeadIsPrime(xs, p, n);
    assert IsPrime(xs[0]);
    var x := xs[0];

    // forall x :: Contains(xs, x) <==> (forall y :: IsPrime(y) && 2 <= y <= p ==> x % y != 0)

    sieved := new int[0];
    assert SievedUpTo(sieved, x, 0);



    var i := 0;
    while(i < xs.Length)
    invariant i <= xs.Length
    ///invariant forall k :: 0 <= k < sieved.Length ==> sieved[k] % x != 0
    //invariant forall k :: 0 <= k < i ==> k < xs.Length && (xs[k] % x != 0) ==> Contains(sieved, xs[k])
    //invariant sieved.Length <= i
    //invariant SievedUpTo(sieved, x, i)
    {
        if(xs[i] % x != 0) {
            sieved := Append(sieved, xs[i]);
        }
        i := i + 1;
    }

    // forall x :: Contains(xs, x) <==> (forall y :: IsPrime(y) && 2 <= y <= p ==> x % y != 0)
    NoPrimesBeforeSievedHead(xs, p, n);
    //assert forall x :: Contains(sieved, x) <==> (forall y :: IsPrime(y) && 2 <= y <= p ==> x % y != 0);
}



// Filters away all multiples of m from an array xs, except m itself.
// TODO possibly good to have:
// * array uniqueness
// * array increasing
method RemoveMultiples(xs: array<int>, m: int) returns (sieved: array<int>)
requires m > 0
// Result doesn't contain what it shouldn't.
ensures forall k :: 0 <= k < sieved.Length ==> sieved[k] % m != 0 || sieved[k] == m
// Keeps what should be preserved.
ensures forall k :: 0 <= k < xs.Length ==> (xs[k] % m != 0 || xs[k] == m) ==> Contains(sieved, xs[k])
ensures sieved.Length <= xs.Length
{
    sieved := new int[0];
    var i := 0;
    while(i < xs.Length)
    decreases xs.Length - i
    invariant i <= xs.Length
    invariant forall k :: 0 <= k < sieved.Length ==> sieved[k] % m != 0 || sieved[k] == m
    invariant forall k :: 0 <= k < i ==> k < xs.Length && (xs[k] % m != 0 || xs[k] == m) ==> Contains(sieved, xs[k])
    invariant sieved.Length <= i
    {
        if(xs[i] % m != 0 || xs[i] == m) {
            sieved := Append(sieved, xs[i]);
        }
        i := i + 1;
    }
}

// Creates an array containing integers in the interval [low, high)
method Range(low: int, high: int) returns (arr: array<int>)
requires high - low >= 0
ensures arr.Length == high - low
ensures forall i :: 0 <= i < high - low ==> arr[i] == low + i
ensures forall x :: Contains(arr, x) ==> low <= x < high
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
}

// Computes an array of primes up to and including n
// Currently indeed outputs primes, but *not* the actual Eratosthene's sieve yet
method Eratosthenes(n: int) returns (primes: array<int>)
requires n >= 2
{
    primes := Range(2, n);
    var m := 2;
    while(m < n)
    {
        primes := RemoveMultiples(primes, m);
        m := m + 1;
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
    var primes := Eratosthenes(100);
    PrintArr(primes);
}