package alabast

import munit.FunSuite
import alabast.macros._
import Context._

class MaterialSpec extends FunSuite:
  type LL[A] = [X] =>> Either[Unit, (A, X)]
  type CC[A] = [X] =>> Either[A, (A, X)]


  testEquals("mu[00]")(mu[[X] =>> (Int, X)](x => int * x).show, "zero")
  testEquals("mu[10]")(mu[[X] =>> Int](_ => int).show, "int")
  testEquals("mu[10]")(mu[[X] =>> Fix[LL[Int]]](_ => mu[LL[Int]](x => one + int * x)).show, "mu(x0 => int * x0 + one)")
  testEquals("mu[20]")(mu[LL[Int]](x => one + int * x).show, "mu(x0 => int * x0 + one)")
  testEquals("mu[20]")(
    mu[LL[Fix[LL[Int]]]](x => one + mu[LL[Int]](y => one + int * y) * x).show,
    "mu(x0 => mu(x1 => int * x1 + one) * x0 + one)"
  )
  testEquals("mu[30]")(mu[CC[Int]](x => int + int * x).show, "mu(x0 => int * x0 + one) * int")
  testEquals("mu[30]")(
    mu[CC[Fix[LL[Int]]]](x => mu[LL[Int]](y => one + int * y) + mu[LL[Int]](y => one + int * y) * x).show,
    "mu(x0 => mu(x1 => int * x1 + one) * x0 + one) * mu(x0 => int * x0 + one)"
  )
  
  given [A] as Functor[LL[A]]:
    def [B, C] (fa: LL[A][B]) map (f: B => C): LL[A][C] = fa.map((i, a) => (i, f(a)))

  def list[A](a: Material[A, ?]): Material[List[A], ?] =
    mu[LL[A]](x => one + a * x).imap {
      _.fold[List[A]] {
        case Left(()) => Nil
        case Right((head, tail)) => head :: tail
      }
    } {
      _.foldRight(Fix[LL[A]](Left(())))((head, tail) => Fix(Right((head, tail))))
    }

  testEquals((int * list(int)).expr, mu[CC[Int]](x => int + int * x).expr)
  testEquals(list(int).unapply(List()), Right(()))
  testEquals(list(int).unapply(List(1, 2)), Left((1, Left((2, Right(()))))))
