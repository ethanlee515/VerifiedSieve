predicate Contains(xs: array<int>, x: int)
reads xs
{
    exists i :: 0 <= i < xs.Length && xs[i] == x
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

// Filters away all multiples of m from an array xs
method RemoveMultiples(xs: array<int>, m: int) returns (sieved: array<int>)
requires m > 0
ensures forall k :: 0 <= k < sieved.Length ==> sieved[k] % m != 0
ensures forall k :: 0 <= k < xs.Length ==> xs[k] % m != 0 ==> Contains(sieved, xs[k])
ensures sieved.Length <= xs.Length
{
    sieved := new int[0];
    var i := 0;
    while(i < xs.Length)
    decreases xs.Length - i
    invariant i <= xs.Length
    invariant forall k :: 0 <= k < sieved.Length ==> sieved[k] % m != 0
    invariant forall k :: 0 <= k < i ==> k < xs.Length && xs[k] % m != 0 ==> Contains(sieved, xs[k])
    invariant sieved.Length <= i
    {
        if(xs[i] % m != 0) {
            sieved := Append(sieved, xs[i]);
        }
        i := i + 1;
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
    var xs := new int[][11, 22, 33, 44, 55, 66, 77];
    var ys := RemoveMultiples(xs, 3);
    PrintArr(ys);
}