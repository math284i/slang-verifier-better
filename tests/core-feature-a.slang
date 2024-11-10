// Passing example:
method m(x: Int) {
    var y: Int := x + 15;
    match {
      x > 0 =>
        assert y/x > 0,
      true =>
        y := 5
    };
    assert y > 0
}

// Failure example:
// method m(x: Int): Int
// requires x >= 0
// ensures result >= 0
// // false: (consider execution when x = 1)
// ensures result == 3 * x
// {
// var acc: Int := 0;
// acc := x / 2;
// acc := acc * 6;
//
// return acc
// }
