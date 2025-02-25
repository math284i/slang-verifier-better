// Passing example:
method sumn(n: Int): Int
    requires n >= 0
{
    var acc: Int := 0;
    var i: Int := 0;
    loop 
        invariant i >= 0
        invariant i <= n
        invariant acc == i * (i + 1) / 2
    {
        i < n =>
            i := i + 1;
            acc := acc + i
    };
    assert i == n;
    assert acc == n * (n + 1) / 2;
    assert false;
    return acc
}

// Failure example:
// method iter(n: Int): Int
// requires n >= 0
// {
// var i: Int := 0;
// loop
// // false: when the loop terminates, i == n + 1
// invariant i <= n
// {
// i <= n => i := i + 1
// }
// }

