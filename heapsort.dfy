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

predicate SortedSequence(q: seq<int>)
{
	forall i,j :: 0 <= i <= j < |q| ==> q[i] <= q[j]
}

method MaxHeap(a: array<int>, i: int)
  requires a != null
	requires 0 <= i <= a.Length
{
  var z := 1;
  while(z < i)
  modifies a
  {
    if(a[z] > a[(z - 1)/2])
    {
      var y := z;

      while(a[y > a])


    }
    z := z + 1;
  }
}
/*
method HeapSort (a:array<int>)
  requires a != null
  modifies a
  ensures sorted(a)
{
  var c := 0;
  var n := a.Length;
  

}
*/
