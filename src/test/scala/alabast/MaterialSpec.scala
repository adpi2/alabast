package alabast

import munit.FunSuite
import alabast.macros._
import Context._

class MaterialSpec extends FunSuite:
  testEquals(zero.isos.size, 0)
  testEquals(one.isos.size, 1)
  testEquals(int.isos.size, 1)
  testEquals((int + string).isos.size, 1)
  testEquals((int * string).isos.size, 1)
  testEquals((3 * string).isos.size, 6)
  testEquals(list(one + one).isos.size, 2)

  val x = int + string + int
  val y = string + int + int
  testEquals(x.as(y).size, 2)
  
  val xAsY = x.as(y)
  val f = xAsY(0)
  val g = xAsY(1)

  testEquals(f.apply(Left(Left(1))), Right(1))
  testEquals(f.unapply(Right(1)), Left(Left(1)))
  testEquals(g.apply(Left(Left(1))), Left(Right(1)))
  testEquals(g.unapply(Left(Right(1))), Left(Left(1)))

  type LL[A] = [X] =>> Either[Unit, (A, X)]
  type CC[A] = [X] =>> Either[A, (A, X)]

  def list[A](a: Context ?=> Material[A, ?])(using Context): Material[List[A], ?] =
    mu[LL[A], List[A]](x => one + a * x)(
      Iso({
        case Left(()) => Nil
        case Right((head, tail)) => head :: tail
      }, {
        case Nil => Left(())
        case head :: tail => Right((head, tail))
      })
    )

  def consList[A](a: Context ?=> Material[A, ?])(using Context): Material[::[A], ?] =
    mu[CC[A], ::[A]](x => a + a * x)(
      Iso({
        case Left(a) => ::(a, Nil)
        case Right((head, tail)) => ::(head, tail)
      }, {
        case a :: Nil => Left(a)
        case head :: (tail @ ::(_, _)) => Right((head, tail))
      })
    )

  // x => one + (y => one + y * x)

  testEquals("mu[00]")(mu(x => int * x)(Iso.fix[[X] =>> (Int, X)]).show, "zero")
  testEquals("mu[10]")(mu[[X] =>> Int, Int](_ => int)(Auto.identity).show, "int")
  testEquals("mu[20]")(list(int).show, "mu(x0 => int * x0 + one)")
  testEquals("mu[20]")(list(list(int)).show, "mu(x0 => mu(x1 => int * x1 + one) * x0 + one)")
  testEquals("mu[30]")(consList(int).show, "mu(x0 => int * x0 + one) * int")
  testEquals("mu[30]")(consList(list(int)).show, "mu(x0 => mu(x1 => int * x1 + one) * x0 + one) * mu(x0 => int * x0 + one)")

  testEquals((int * list(int)).expr, consList(int).expr)
  testEquals(list(int).cons.unapply(List()), Right(()))
  testEquals(list(int).cons.unapply(List(1, 2)), Left((1, Left((2, Right(()))))))

  testEquals(list(one + one).autos.size, 2)
  val h = (0)

  testEquals(
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

  
  testEquals(mu[A, Fix[A]](x => one + (x + x))(Iso.fix).autos.size, 2)
  testEquals(
    mu[A, Fix[A]](x => one + (x + x))(Iso.fix).autos.map(_.apply(aRight(aLeft(aUnit)))),
    Seq(
      aLeft(aRight(aUnit)),
      aRight(aLeft(aUnit))
    )
  )

  type B[X] = Either[Unit, (X, List[(Either[Int, Int], X)])]
  def bUnit: Fix[B] = Fix(Left(()))
  def b(fst: Fix[B], snd: List[(Either[Int, Int], Fix[B])]): Fix[B] = Fix(Right((fst, snd)))
  
  testEquals(mu[B, Fix[B]](x => one + x * list((int + int) * x))(Iso.fix).autos.size, 2)
  testEquals(
    mu[B, Fix[B]](x => one + x * list((int + int) * x))(Iso.fix).autos
      .map(_.apply(b(bUnit, List((Right(5), b(bUnit, List((Left(6), bUnit)))))))),
    Seq(
      b(bUnit, List((Left(5), b(bUnit, List((Right(6), bUnit)))))),
      b(bUnit, List((Right(5), b(bUnit, List((Left(6), bUnit))))))
    )
  )
