package alabast

import munit.FunSuite
import alabast.macros.TestSuite
import Context._

class ExprSpec extends TestSuite:
  def list[A](a: Context ?=> Material[A, ?])(using Context): Material[List[A], ?] =
    mu[[X] =>> Either[Unit, (A, X)], List[A]](x => one + a * x)(
      Iso({
        case Left(()) => Nil
        case Right((head, tail)) => head :: tail
      }, {
        case Nil => Left(())
        case head :: tail => Right((head, tail))
      })
    )
  def consList[A](a: Context ?=> Material[A, ?])(using Context): Material[::[A], ?] =
    mu[[X] =>> Either[A, (A, X)], ::[A]](x => a + a * x)(
      Iso({
        case Left(a) => ::(a, Nil)
        case Right((head, tail)) => ::(head, tail)
      }, {
        case a :: Nil => Left(a)
        case head :: (tail @ ::(_, _)) => Right((head, tail))
      })
    )

  testEquals("Zero.autos")(zero.isos.size, 0)
  testEquals("One.autos")(one.isos.size, 1)
  testEquals("Predef.autos")(int.isos.size, 1)
  testEquals("Sum.autos")((int + string).isos.size, 1)
  testEquals("Product.autos")((int * string).isos.size, 1)
  testEquals("Repeat.autos")((3 * string).isos.size, 6)
  testEquals("Power.autos")((string^3).isos.size, 6)
  testEquals("Repeat.autos")((3 * (string^3)).isos.size, 1296)

  testEquals("show[0]")(zero.show, "zero")
  
  testAssert("compare[00]")(int + one > string + one)
  testAssert("compare[01]")(int + one < int + string)
  testAssert("compare[10]")(int + one > string)
  testAssert("compare[11]")(int + one > int)
  testAssert("compare[20]")(int > string + one)
  testAssert("compare[21]")(string < string + one)
  testAssert("compare[30]")(2 * int > 3 * string)
  testAssert("compare[31]")(3 * int > 2 * int)
  testAssert("compare[40]")(2 * int > string)
  testAssert("compare[41]")(2 * int > int)
  testAssert("compare[50]")(int > 2 * string)
  testAssert("compare[51]")(int < 2 * int)
  testAssert("compare[60]")(int * string > long * string)
  testAssert("compare[61]")(int * string < int * long)
  testAssert("compare[70]")(long * string < int)
  testAssert("compare[71]")(long * string > long)
  testAssert("compare[80]")(int > long * string)
  testAssert("compare[81]")(int < int * string)
  testAssert("compare[90]")((int^2) > (string^3))
  testAssert("compare[91]")((string^2) < (string^3))
  testAssert("compare[A0]")((string^2) < int)
  testAssert("compare[A1]")((string^2) > string)
  testAssert("compare[B0]")(string < (int^2))
  testAssert("compare[B1]")(string < (string^2))
  testAssert("compare[C0]")(list(int) > list(string))
  testAssert("compare[C1]")(list(int) > (int^2) + int + one)
  testAssert("compare[C2]")(int > list(string))

  testEquals("+[00]")((zero + one).show, "one")
  testEquals("+[10]")((int + zero).show, "int")
  testEquals("+[20]")(((int + one) + (int + string)).show, "2 * int + string + one")
  testEquals("+[21]")(((int + one) + (string + one)).show, "int + string + 2 * one")
  testEquals("+[22]")(((string + one) + (int + string)).show, "int + 2 * string + one")
  testEquals("+[30]")(((int + one) + int).show, "2 * int + one")
  testEquals("+[31]")(((int + one) + string).show, "int + string + one")
  testEquals("+[32]")(((string + one) + int).show, "int + string + one")
  testEquals("+[40]")((string + (string + one)).show, "2 * string + one")
  testEquals("+[41]")((int + (string + one)).show, "int + string + one")
  testEquals("+[42]")((string + (int + one)).show, "int + string + one")
  testEquals("+[50]")((2 * string + string).show, "3 * string")
  testEquals("+[51]")((2 * string + one).show, "2 * string + one")
  testEquals("+[52]")((2 * string + int).show, "int + 2 * string")

  testEquals("*[00]")((zero * one).show, "zero")
  testEquals("*[10]")((one * zero).show, "zero")
  testEquals("*[20]")((one * int).show, "int")
  testEquals("*[30]")((int * one).show, "int")
  testEquals("*[40]")(((int + one) * int).show, "int^2 + int")
  testEquals("*[50]")((int * (int + one)).show, "int^2 + int")
  testEquals("*[60]")((2 * int * (2 * string)).show, "4 * int * string")
  testEquals("*[61]")((2 * string * (2 * int)).show, "4 * int * string")
  testEquals("*[70]")((2 * int * string).show, "2 * int * string")
  testEquals("*[71]")((2 * string * int).show, "2 * int * string")
  testEquals("*[80]")((int * (2 * string)).show, "2 * int * string")
  testEquals("*[81]")((string * (int + int)).show, "2 * int * string")
  testEquals("*[90]")(((int * string) * (int * long)).show, "int^2 * long * string")
  testEquals("*[91]")(((int * string) * (long * string)).show, "int * long * string^2")
  testEquals("*[92]")(((long * string) * (int * string)).show, "int * long * string^2")
  testEquals("*[A0]")(((int * string) * (int^2)).show, "int^3 * string")
  testEquals("*[A1]")(((int * string) * string).show, "int * string^2")
  testEquals("*[A2]")(((long * string) * int).show, "int * long * string")
  testEquals("*[B0]")(((int^2) * ((int^2) * string)).show, "int^4 * string")
  testEquals("*[B1]")((int * (long * string)).show, "int * long * string")
  testEquals("*[B2]")((string * (int * string)).show, "int * string^2")
  testEquals("*[C0]")((string * string).show, "string^2")
  testEquals("*[C1]")((string * int).show, "int * string")

  testEquals("^[00]")((zero^2).show, "zero")
  testEquals("^[10]")((one^3).show, "one")
  testEquals("^[20]")(((int + string)^2).show, "int^2 + 2 * int * string + string^2")
  testEquals("^[30]")(((2 * int)^3).show, "8 * int^3")
  testEquals("^[40]")(((int * string)^2).show, "int^2 * string^2")
  testEquals("^[50]")((int^2^3).show, "int^6")

  testEquals("subtract[00]")(one.expr.subtract(zero.expr).get.show, "one")
  testEquals("subtract[10]")((int + string).expr.subtract((2 * int + string).expr), None)
  testEquals("subtract[11]")((int + string).expr.subtract((int + one).expr), None)
  testEquals("subtract[12]")((int + string).expr.subtract((int + string).expr).get.show, "zero")
  testEquals("subtract[13]")((int + string + one).expr.subtract((int + string).expr).get.show, "one")
  testEquals("subtract[14]")((2 * int + string + one).expr.subtract((int + string).expr).get.show, "int + one")
  testEquals("subtract[15]")((int + string).expr.subtract((int + one).expr), None)
  testEquals("subtract[16]")((int + string + one).expr.subtract((string + one).expr).get.show, "int")
  testEquals("subtract[17]")((int + 2 * string + one).expr.subtract((string + one).expr).get.show, "int + string")
  testEquals("subtract[18]")((string + one).expr.subtract((int + string).expr), None)
  testEquals("subtract[20]")((int + string).expr.subtract((2 * int).expr), None)
  testEquals("subtract[21]")((int + string).expr.subtract(int.expr).get.show, "string")
  testEquals("subtract[22]")((2 * int + string).expr.subtract(int.expr).get.show, "int + string")
  testEquals("subtract[23]")((int + string).expr.subtract(one.expr), None)
  testEquals("subtract[24]")((int + string).expr.subtract(string.expr).get.show, "int")
  testEquals("subtract[25]")((int + string + one).expr.subtract(string.expr).get.show, "int + one")
  testEquals("subtract[26]")((string + one).expr.subtract(int.expr), None)
  testEquals("subtract[30]")(string.expr.subtract(string.expr).get.show, "zero")
  testEquals("subtract[31]")((2 * string).expr.subtract(string.expr).get.show, "string")
  testEquals("subtract[32]")((4 * string).expr.subtract((2 * string).expr).get.show, "2 * string")
  testEquals("subtract[33]")(string.expr.subtract(int.expr), None)

  testEquals("asProduct[00]")(zero.asProduct(int).get.snd, zero.expr)
  testEquals("asProduct[10]")(int.asProduct(one).get.snd, int.expr)
  testEquals("asProduct[20]")((string + one).asProduct(int + string), None)
  testEquals("asProduct[21]")((int * string + one).asProduct(int + one), None)
  testEquals("asProduct[22]")((int * string + string + one).asProduct(int + one), None)
  testEquals("asProduct[23]")((int * string + string).asProduct(int + one).get.snd, string.expr)
  testEquals("asProduct[24]")((int * string + int + string + one).asProduct(int + one).get.snd, (string + one).expr)
  testEquals("asProduct[30]")((int + one).asProduct(string), None)
  testEquals("asProduct[31]")((int + string).asProduct(int), None)
  testEquals("asProduct[32]")((int * string + int).asProduct(int).get.snd, (string + one).expr)
  testEquals("asProduct[40]")(int.asProduct(int + one), None)
  testEquals("asProduct[50]")((4 * int).asProduct(2 * string), None)
  testEquals("asProduct[51]")((2 * int * string).asProduct(2 * int).get.snd, string.expr)
  testEquals("asProduct[52]")((4 * int * string).asProduct(2 * int).get.snd, (2 * string).expr)
  testEquals("asProduct[53]")((3 * int).asProduct(2 * int), None)
  testEquals("asProduct[60]")((3 * int).asProduct(string), None)
  testEquals("asProduct[61]")((3 * int).asProduct(int).get.snd, (3 * one).expr)
  testEquals("asProduct[70]")(int.asProduct(3 * int), None)
  testEquals("asProduct[80]")((int * string).asProduct((int^2) * long), None)
  testEquals("asProduct[81]")((int * string).asProduct(int * long), None)
  testEquals("asProduct[82]")((int * (string^2)).asProduct(int * string).get.snd, string.expr)
  testEquals("asProduct[83]")(((int^2) * string).asProduct(int * string).get.snd, int.expr)
  testEquals("asProduct[84]")(((int^2) * long * string).asProduct(int * string).get.snd, (int * long).expr)
  testEquals("asProduct[85]")((int * string).asProduct(long * string), None)
  testEquals("asProduct[86]")((int * string * string).asProduct(string * string).get.snd, int.expr)
  testEquals("asProduct[87]")((long * string).asProduct(int), None) 
  testEquals("asProduct[90]")((int * string).asProduct(int).get.snd, string.expr)
  testEquals("asProduct[91]")(((int^2) * string).asProduct(int).get.snd, (int * string).expr)
  testEquals("asProduct[92]")((int * long).asProduct(string), None)
  testEquals("asProduct[93]")((int * string).asProduct(string).get.snd, int.expr)
  testEquals("asProduct[A0]")(int.asProduct(int * string), None)
  testEquals("asProduct[B0]")((int^3).asProduct(int^3).get.snd, one.expr)
  testEquals("asProduct[B1]")((int^3).asProduct(int^2).get.snd, int.expr)
  testEquals("asProduct[B2]")((int^3).asProduct(int).get.snd, (int^2).expr)
  testEquals("asProduct[B3]")((int^2).asProduct(int^3), None)

  testEquals("mu[00]")(mu(x => int * x)(Iso.fix[[X] =>> (Int, X)]).show, "zero")
  testEquals("mu[10]")(mu[[X] =>> Int, Int](_ => int)(Auto.identity).show, "int")
  testEquals("mu[20]")(list(int).show, "mu(x0 => int * x0 + one)")
  testEquals("mu[20]")(list(list(int)).show, "mu(x0 => mu(x1 => int * x1 + one) * x0 + one)")
  testEquals("mu[20]")(list(int).cons.unapply(List()), Right(()))
  testEquals("mu[20]")(list(int).cons.unapply(List(1, 2)), Left((1, Left((2, Right(()))))))
  testEquals("mu[30]")(consList(int).show, "mu(x0 => int * x0 + one) * int")
  testEquals("mu[30]")(consList(list(int)).show, "mu(x0 => mu(x1 => int * x1 + one) * x0 + one) * mu(x0 => int * x0 + one)")

  type C[X] = Either[Unit, List[X]]
  testEquals("mu[30]")(mu[C, Fix[C]](x => one + list(x))(Iso.fix).show, "mu(x0 => mu(x1 => x0 * x1 + one) + one)")
  testEquals("mu[30]")(mu[C, Fix[C]](x => one + list(x))(Iso.fix).autos.size, 1)

  testEquals("Mu.autos")(list(one + one).autos.size, 2)
  testEquals("Mu.autos")(
    list(one + one).autos.map(_.apply(List(Left(()), Right(()), Left(())))),
    Seq(
      List(Right(()), Left(()), Right(())),
      List(Left(()), Right(()), Left(()))
    )
  )

  type A[X] = Either[Unit, Either[X, X]]
  def aUnit = Fix[A](Left(()))
  def aLeft(a: Fix[A]): Fix[A] = Fix(Right(Left(a)))
  def aRight(a: Fix[A]): Fix[A] = Fix[A](Right(Right(a)))
  testEquals("Mu.autos")(mu[A, Fix[A]](x => one + (x + x))(Iso.fix).autos.size, 2)
  testEquals("Mu.autos")(
    mu[A, Fix[A]](x => one + (x + x))(Iso.fix).autos.map(_.apply(aRight(aLeft(aUnit)))),
    Seq(
      aLeft(aRight(aUnit)),
      aRight(aLeft(aUnit))
    )
  )

  type B[X] = Either[Unit, (X, List[(Either[Int, Int], X)])]
  def bUnit: Fix[B] = Fix(Left(()))
  def b(fst: Fix[B], snd: List[(Either[Int, Int], Fix[B])]): Fix[B] = Fix(Right((fst, snd)))
  
  testEquals("Mu.autos")(mu[B, Fix[B]](x => one + x * list((int + int) * x))(Iso.fix).autos.size, 2)
  testEquals("Mu.autos")(
    mu[B, Fix[B]](x => one + x * list((int + int) * x))(Iso.fix).autos
      .map(_.apply(b(bUnit, List((Right(5), b(bUnit, List((Left(6), bUnit)))))))),
    Seq(
      b(bUnit, List((Left(5), b(bUnit, List((Right(6), bUnit)))))),
      b(bUnit, List((Right(5), b(bUnit, List((Left(6), bUnit))))))
    )
  )

  testEquals("unmu")(list(int).unmu.show, "mu(x0 => int * x0 + one) * int + one")
  testEquals("unmu")(list(list(int)).unmu.show, "mu(x0 => mu(x1 => int * x1 + one) * x0 + one) * mu(x0 => int * x0 + one) + one")
  lazy val cons: Iso[?, List[List[Int]]] = list(list(int)).unmu.cons
  testEquals("unmu")(cons.apply(cons.unapply(List(List(1, 2), List(3, 4)))), List(List(1, 2), List(3, 4)))

  type Z[X] = Either[(List[X], X), Unit]
  testEquals("unmu")(mu[Z, Fix[Z]](x => list(x) * x + one)(Iso.fix).unmu.show, "mu(x0 => mu(x1 => x0 * x1 + one) * x0 + one)^2 + one")

  testEquals("asTermOf[00]")(one.asTermOf(zero).size, 0)
  testEquals("asTermOf[10]")((2 * int + string).asTermOf(int + string).size, 0)
  testEquals("asTermOf[11]")((int + string).asTermOf(int + long).size, 0)
  testEquals("asTermOf[12]")((int + string).asTermOf(int + long + string).size, 1)
  testEquals("asTermOf[13]")((int + string).asTermOf(long + string).size, 0)
  testEquals("asTermOf[14]")((long + string).asTermOf(int + long).size, 0)
  testEquals("asTermOf[15]")((long + string).asTermOf(int + long + string).size, 1)
  testEquals("asTermOf[20]")((int + string).asTermOf(int).size, 0)
  testEquals("asTermOf[30]")((2 * int).asTermOf(int + string).size, 0)
  testEquals("asTermOf[31]")(int.asTermOf(2 * int + string).size, 2)
  testEquals("asTermOf[32]")(int.asTermOf(long + string).size, 0)
  testEquals("asTermOf[33]")(long.asTermOf(int + string).size, 0)
  testEquals("asTermOf[34]")(long.asTermOf(int + long).size, 1)
  testEquals("asTermOf[40]")((2 * long).asTermOf(2 * long).size, 2)
  testEquals("asTermOf[41]")(long.asTermOf(3 * long).size, 3)
  testEquals("asTermOf[42]")((2 * long).asTermOf(3 * long).size, 6)
  testEquals("asTermOf[43]")((3 * long).asTermOf(2 * long).size, 0)
  testEquals("asTermOf[44]")(long.asTermOf(2 * int).size, 0)

  testEquals("primeFactors")(((int^2) + int * long).expr.primeFactors, List(int, int + long).map(_.expr))
  testEquals("primeFactors")(((int^2) + 2 * int * long + (long^2)).expr.primeFactors, List(int + long, int + long).map(_.expr))
  testEquals("primeFactors")((6 * (int^2) + 5 * int + one).expr.primeFactors, List(2 * int + one, 3 * int + one).map(_.expr))
  testEquals("primeFactors")(
    ((int^2) + 2 * int * long + int * string + 2 * int + (long^2) + long * string + 2 * long + string + one).expr.primeFactors,
    List(int + long + one, int + long + string + one).map(_.expr)
  )
  testEquals("primeFactors")(
    (2 * int * long * string + 2 * int * long + 2 * int * string + 2 * int + 2 * long * string + 2 * long + 2 * string + 2 * one).expr.primeFactors,
    List(2 * one, string + one, long + one, int + one).map(_.expr)
  )

