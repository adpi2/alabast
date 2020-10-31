package alabast

case class Iso[A, B](apply: A => B, unapply: B => A)

object Iso:
  def absurd[A]: Iso[Nothing, A] = Iso(x => x, x => throw new Exception(""))

  def product[A, B, C, D](x: Iso[A, C], y: Iso[B, D]) = 
    Iso[(A, B), (C, D)]((a, b) => (x.apply(a), y.apply(b)), (c, d) => (x.unapply(c), y.unapply(d)))

  def sum[A, B, C, D](x: Iso[A, C], y: Iso[B, D]) = 
    Iso[Either[A, B], Either[C, D]](
      _.left.map(x.apply).map(y.apply),
      _.left.map(x.unapply).map(y.unapply)
    )

  def lazily[A, B](iso: => Iso[A, B]) = Iso(x => iso.apply(x), x => iso.unapply(x))

  def fix[F[_]]: Iso[F[Fix[F]], Fix[F]] = Iso(Fix.apply, _.unfix)

  extension [A, B] (x: Iso[A, B])
    def invert: Iso[B, A] = Iso(x.unapply, x.apply)

  extension [A, B, C] (x: Iso[A, B])
    def andThen(y: Iso[B, C]): Iso[A, C] =
      Iso(x.apply andThen y.apply, y.unapply andThen x.unapply)

type Auto[A] = Iso[A, A]

object Auto:
  def apply[A](apply: A => A, unapply: A => A): Auto[A] = Iso(apply, unapply)
  def identity[A]: Auto[A] = Iso[A, A](x => x, x => x)
