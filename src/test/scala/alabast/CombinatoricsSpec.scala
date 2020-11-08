package alabast

import munit.FunSuite
import alabast.macros._
import Context._

class PermutationSpec extends FunSuite:
  testEquals(permutations(2).size, 2)
  testEquals(permutations(3).size, 6)
  testEquals(permutations(4).size, 24)
  testEquals(permutations(5).size, 120)
  testEquals(permutations(6).size, 720)
