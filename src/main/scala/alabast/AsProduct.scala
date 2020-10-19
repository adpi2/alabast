package alabast

final case class AsProduct[X, Y, R](underlying: Material[(X, Y), R], snd: Expr[Y]):
  type Raw = R
  type Snd = Y
  val apply = underlying.apply
  val unapply = underlying.unapply
  