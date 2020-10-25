package alabast

case class Fix[F[_]](unfix: F[Fix[F]]):
  def fold[A](alg: F[A] => A)(using Functor[F]): A =
    alg(unfix.map(_.fold(alg)))
