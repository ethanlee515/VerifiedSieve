include "libraries/src/NonlinearArithmetic/DivMod.dfy"
include "libraries/src/NonlinearArithmetic/Mul.dfy"

import opened DivMod
import opened Mul

// Checks if an integer is prime.
predicate IsPrime(x: int)
{
    x >= 2 && forall y :: 2 <= y < x ==> x % y != 0
}

lemma {:axiom} Test(n: int)
requires n >= 2
ensures exists p :: IsPrime(p) && n % p == 0
{
    // Dafny complains here.
    // It is as if my {:axiom} annotation is ignored...
}

lemma PrimeDivisorExists(n: int)
decreases n - 2
requires n >= 2
//ensures exists p :: IsPrime(p) && n % p == 0
{
    if(!IsPrime(n)) {
        var m :| 2 <= m < n && n % m == 0;
        Test(m); // treat as axiom for now
        //PrimeDivisorExists(m);
        var p :| IsPrime(p) && m % p == 0;
        assert n == m * (n / m);
        assert p >= 2;
        assert n % p == (m * (n / m)) % p;
        LemmaMulModNoopLeft(m, n / m, p);
        assert (m % p) * (n / m) % p == m * (n / m) % p;
        assert 0 * (n / m) % p == m * (n / m) % p;
        assert 0 % p == m * (n / m) % p;
        LemmaMulBasics(p);
        assert 0 * p == 0;
        //uncommenting next line breaks the proof.
        assert p >= 2;
    }
}

        
        //assert 0 == 0 * p;
        //LemmaModMultiplesBasic(0, p);
        //assert 0 % p == 0;


            /*
            assert 0 < p;
            
            */
            //Uncommenting next line breaks the proof.
            //assert 0 == 0 * p;
            

            //assert 0 % p == (0 * p) % p;
            //LemmaModMultiplesBasic(0, p);
            //assert (0 * p) % p == 0;
            //assert m * (n / m) % p == 0;

// Checks what the name suggests
predicate Contains(xs: array<int>, x: int)
reads xs
{
    exists i :: 0 <= i < xs.Length && xs[i] == x
}

// Checks if an array is *strictly* increasing.
// Note: this implies uniqueness.
predicate Increases(xs: array<int>)
reads xs
{
    forall i, j :: 0 <= i < j < xs.Length ==> xs[i] < xs[j]
}

lemma CompositeTest()
ensures !IsPrime(209)
{
    var y := 11;
    assert 209 % y == 0;
}

lemma PrimeTest()
ensures !IsPrime(0)
ensures IsPrime(2)
ensures IsPrime(3)
ensures !IsPrime(4)
ensures IsPrime(5)
ensures !IsPrime(6)
ensures !IsPrime(11 * 17)
ensures IsPrime(127)
{
    var x := 4 % 2;
    x := 6 % 2;
    x := (11 * 17) % 11;
}

/*
{
    if(IsPrime(n)) {
        var d := n;
        var z := d % n;
        assert IsPrime(n) && n % n == 0;
        assert exists x :: IsPrime(x) && n % x == 0;
    } else {
        var m :| 2 <= m < n && n % m == 0;
        assert 2 <= m < n;
        assert 0 <= m < n;
        PrimeDivisorExists(m);
        /*
        PrimeDivisorExists(m);
        var p :| IsPrime(p) && m % p == 0;
        assert n == m * (n / m);
        assert m % p == 0;
        assert (m * (n / m)) % p == 0;
        assert n % p == 0;
        assert IsPrime(p);
        assert IsPrime(p) && n % p == 0;
        assert exists x :: IsPrime(x) && n % x == 0;
    }
    assert exists x :: IsPrime(x) && n % x == 0;
    var x :| IsPrime(x) && n % x == 0; */
    }
}
*/

// Removes the i-th element of an array.
method RemoveIth(xs: array<int>, i: int) returns (ys: array<int>)
requires xs.Length >= 1
requires 0 <= i < xs.Length
ensures ys.Length == xs.Length - 1
ensures forall k :: 0 <= k < i ==> xs[k] == ys[k]
ensures forall k :: i + 1 <= k < xs.Length ==> xs[k] == ys[k - 1]
ensures forall k :: (0 <= k < xs.Length && k != i) ==> Contains(ys, xs[k])
{
    ys := new int[xs.Length - 1];
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
    ys := new int[xs.Length + 1];
    var j := 0;
    while(j < xs.Length)
    invariant forall k :: 0 <= k < j ==> k < xs.Length && ys[k] == xs[k]
    {
        ys[j] := xs[j];
        j := j + 1;
    }
    ys[xs.Length] := x;
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
ensures Increases(arr)
{
    var len := high - low;
    arr := new int[len];
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