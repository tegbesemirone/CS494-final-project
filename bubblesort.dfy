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
    var sorted := false;
    var swapped := a.Length;
    // while loop to check if array is sorted
    while(!sorted)
        invariant 0 <= iter <= a.Length
        invariant forall k, l :: 0 <= k < iter <= l < a.Length ==> a[k] <= a[l]

    {
        var sortCheck := 0;
        var stop := a.Length-1;
        // nested if condition checks to see if we need to swap values
        while(iter < stop)
            decreases stop - iter
        {
            if(a[iter] > a[iter+1])
            {
                a[iter], a[iter+1] := a[iter+1], a[iter];
                sortCheck := sortCheck + 1;
            }
           iter := iter + 1; 
        }
        if(sortCheck < 1)
        {
            sorted := true;
        }

    }

}