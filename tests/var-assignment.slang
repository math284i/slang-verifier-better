method sumn(n: Int): Int
    requires n >= 0
{
    var acc: Int := 0;
    assert acc > 0; // Now this error should surface
    var i: Int := 0;
    i := n / acc
}