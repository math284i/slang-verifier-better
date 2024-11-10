// Can only be tested in the GUI:
// method sumn(n: Int): Int
// requires n >= 0
// {
// var acc: Int := 0;
// var i: Int := 0;
// loop
// // Error: Invariant may not be preserved
// invariant i <= n
// {
// i <= n =>
// acc := acc + i;
// i := i + 1
// };
// return acc
// }