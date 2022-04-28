predicate sorted (a: array<int>)
	requires a != null
	reads a
{
	sorted'(a, a.Length)
}

predicate sorted' (a: array<int>, i: int)
	requires a != null
	requires 0 <= i <= a.Length
	reads a
{
	forall k :: 0 < k < i ==> a[k-1] <= a[k]
}

method BubbleSort (a: array<int>)
	requires a != null
	modifies a
	ensures sorted(a)
{
    var iter := 0;
    while(x < a.Length)
        invariant 0 <= x <= a.Length
        invariant forall k, l :: 0 <= k < x <= l < a.Length ==> a[k] <= a[l]
    {
        
    }

}