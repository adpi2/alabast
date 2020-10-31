package alabast

import munit.FunSuite
import alabast.macros._
import Context._

class MaterialSpec extends FunSuite:
  testEquals("Zero.autos")(zero.isos.size, 0)
  testEquals("One.autos")(one.isos.size, 1)
  testEquals("Predef.autos")(int.isos.size, 1)
  testEquals("Sum.autos")((int + string).isos.size, 1)
  testEquals("Product.autos")((int * string).isos.size, 1)
  testEquals("Repeat.autos")((3 * string).isos.size, 6)

  val x = int + string + int
  val y = string + int + int
  testEquals("as")(x.as(y).size, 2)
  testEquals("as")(x.as(y)(0).apply(Left(Left(1))), Right(1))
  testEquals("as")(x.as(y)(0).unapply(Right(1)), Left(Left(1)))
  testEquals("as")(x.as(y)(1).apply(Left(Left(1))), Left(Right(1)))
  testEquals("as")(x.as(y)(1).unapply(Left(Right(1))), Left(Left(1)))

  type LL[A] = [X] =>> Either[Unit, (A, X)]
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

  type CC[A] = [X] =>> Either[A, (A, X)]
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

  testEquals("mu[00]")(mu(x => int * x)(Iso.fix[[X] =>> (Int, X)]).show, "zero")
  testEquals("mu[10]")(mu[[X] =>> Int, Int](_ => int)(Auto.identity).show, "int")
  testEquals("mu[20]")(list(int).show, "mu(x0 => int * x0 + one)")
  testEquals("mu[20]")(list(list(int)).show, "mu(x0 => mu(x1 => int * x1 + one) * x0 + one)")
  testEquals("mu[20]")(list(int).cons.unapply(List()), Right(()))
  testEquals("mu[20]")(list(int).cons.unapply(List(1, 2)), Left((1, Left((2, Right(()))))))
  testEquals("mu[30]")(consList(int).show, "mu(x0 => int * x0 + one) * int")
  testEquals("mu[30]")(consList(list(int)).show, "mu(x0 => mu(x1 => int * x1 + one) * x0 + one) * mu(x0 => int * x0 + one)")
  testEquals("mu[30]")((int * list(int)).expr, consList(int).expr)

  type C[X] = Either[Unit, List[X]]
  testEquals("mu[30]")(mu[C, Fix[C]](x => one + list(x))(Iso.fix).show, "2 * mu(x0 => mu(x1 => 2 * x0 * x1 + one) * x0 + one)")
  testEquals("mu[30]")(mu[C, Fix[C]](x => one + list(x))(Iso.fix).autos.size, 4)
  
  type D[X] = [Y] =>> C[(X, Y)]
  type E[X] = Either[Unit, Fix[D[X]]]
  testEquals("mu[30]")(
    mu[E, Fix[E]](x => one + mu[D[Any], Fix[D[Any]]](y => one + list(x * y))(Iso.fix))(Iso.fix).show,
    "3 * mu(x0 => 2 * mu(x1 => 3 * mu(x2 => 6 * x0 * x1 * x2 + one) * x0 * x1 + one) * mu(x1 => 6 * mu(x2 => 3 * x0 * x1 * x2 + one) * x0 * x1 + one) * x0 + one)"
  )
  // testEquals("mu[30]")(
  //   mu[E, Fix[E]](x => one + mu[D[Any], Fix[D[Any]]](y => one + list(x * y))(Iso.fix))(Iso.fix).autos.size,
  //   223948800
  // )

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
  val z = mu[Z, Fix[Z]](x => list(x) * x + one)(Iso.fix)
  testEquals("unmu")(z.unmu.show, "mu(x0 => mu(x1 => x0 * x1 + one) * x0 + one) * mu(x0 => mu(x1 => x0 * x1 + one) * x0 + one) + one")
