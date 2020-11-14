package alabast

import munit.FunSuite
import alabast.macros._
import Context._

class MaterialSpec extends TestSuite:
  val x = int + string + int
  val y = string + int + int
  testEquals("as")(x.as(y).size, 2)
  testEquals("as")(x.as(y)(0).apply(Left(Left(1))), Right(1))
  testEquals("as")(x.as(y)(0).unapply(Right(1)), Left(Left(1)))
  testEquals("as")(x.as(y)(1).apply(Left(Left(1))), Left(Right(1)))
  testEquals("as")(x.as(y)(1).unapply(Left(Right(1))), Left(Left(1)))

  
