package alabast

import munit.FunSuite
import alabast.macros._
import Context._

class PermutationSpec extends FunSuite:
  testEquals(permutations(1).size, 1)
  testEquals(permutations(2).size, 2)
  testEquals(permutations(3).size, 6)
  testEquals(permutations(4).size, 24)
  testEquals(permutations(5).size, 120)
  testEquals(permutations(6).size, 720)

  testEquals(variations(1, 2).size, 2)
  testEquals(variations(1, 3).size, 3)
  testEquals(variations(2, 3).size, 6)
  testEquals(variations(1, 4).size, 4)
  testEquals(variations(2, 4).size, 12)
  testEquals(variations(3, 4).size, 24)
  testEquals(variations(1, 5).size, 5)
  testEquals(variations(2, 5).size, 20)
  testEquals(variations(3, 5).size, 60)
  testEquals(variations(4, 5).size, 120)
  testEquals(variations(1, 6).size, 6)
  testEquals(variations(2, 6).size, 30)
  testEquals(variations(3, 6).size, 120)
  testEquals(variations(4, 6).size, 360)
  testEquals(variations(5, 6).size, 720)
