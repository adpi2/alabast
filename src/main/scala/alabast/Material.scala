package alabast

import Comparison._

sealed trait Material[T, R]:
  type Raw = R
  val expr: Expr[R]
  val apply: R => T
  val unapply: T => R
  // unsafe cast R to U
  def withRaw[U]: Material[T, U] = asInstanceOf[Material[T, U]]

final case class Raw[T](expr: Expr[T]) extends Material[T, T]:
  override val apply: T => T = identity
  override val unapply: T => T = identity

final case class Typed[T, R](val expr: Expr[R], val apply: R => T, val unapply: T => R) extends Material[T, R]

def zero[T]: Material[T, Nothing] = Typed(Zero, identity, _ => absurd)
def one: Material[Unit, Unit] = Raw(One)
def predef[T](name: String)(using ctx: Context): Material[T, T] = Raw(Predef[T](ctx.variables(name)))
def mu[F[+_]](f: Material[Any, ?] => Context ?=> Material[F[Any], ?])(using ctx: Context): Material[Fix[F], ?] =
  muImpl[F]([X] => (x: Material[X, ?]) => (ctx: Context) ?=> f(x.asInstanceOf[Material[Any, ?]]).asInstanceOf[Material[F[X], ?]])

object Material:
  extension [X, R, Y] (x: Material[X, R])
    def show: String = x.expr.show

    def imap (f: X => Y)(g: Y => X): Material[Y, R] = x match
      case Raw(expr) => Typed(expr, f, g)
      case Typed(expr, apply, unapply) => Typed(expr, apply andThen f, g andThen unapply)
      case _ => absurd // should not be needed

    def + (y: Material[Y, ?]): Material[Either[X, Y], ?] = (x, y) match
      case (Raw(x), Raw(y)) => x + y
      case (Raw(x), y) => (x + y.expr).imap(_.map(y.apply))(_.map(y.unapply))
      case (s, Raw(y)) => (x.expr + y).imap(_.left.map(x.apply))(_.left.map(x.unapply))
      case (x, y) => (x.expr + y.expr).imap
        { _.map(y.apply).left.map(x.apply) }
        { _.map(y.unapply).left.map(x.unapply) }
    
    def * (y: Material[Y, ?]): Material[(X, Y), ?] with { type R <: Any } = (x, y) match
      case (Raw(x), Raw(y)) => x * y
      case (Raw(x), y) =>
        (x * y.expr).imap
          { (x, yy) => (x, y.apply(yy)) }
          { (x, yy) => (x, y.unapply(yy)) }
      case (x, Raw(y)) =>
        (x.expr * y).imap
          { (xx, y) => (x.apply(xx), y) }
          { (xx, y) => (x.unapply(xx), y) }
      case (x, y) => 
        (x.expr * y.expr).imap
          { (xx, yy) => (x.apply(xx), y.apply(yy)) }
          { (xx, yy) => (x.unapply(xx), y.unapply(yy)) }
    
    def asProduct(y: Material[Y, ?]): Option[AsProduct[Y, ?, R]] = y match
      case Raw(y) => x.expr.asProduct(y)
      case Typed(expr, apply, unapply) =>
        for product <- x.expr.asProduct(expr)
        yield
          AsProduct(
            product.underlying.imap
              { (y, x) => (apply(y), x) }
              { (y, x) => (unapply(y), x) },
            product.snd
          ) 

private def muImpl[F[+_]](f: [X] => Material[X, ?] => Context ?=> Material[F[X], ?])(using ctx: Context): Material[Fix[F], ?] =
  val fZero = f(zero)
  val fOne = f(one).expr
  fZero.expr match
    case Zero => zero // 00
    case `fOne` => fZero.imap(Fix.apply)(_.unfix.asInstanceOf[F[Nothing]]) // 10
    case One => // 20
      val (mu, next) = ctx.next
      lazy val recurse = Typed(Predef[unmu.Raw](mu), unmu.apply(_), unmu.unapply(_))
      lazy val unmu: Material[Fix[F], ?] = f(recurse)(using next).imap(Fix.apply)(_.unfix)
      Typed(Mu(mu, unmu.expr), unmu.apply, unmu.unapply)
    case _ => // 30
      val (variable, next) = ctx.next
      
      val fZeroIn = f(zero)(using next)
      type RawMu = fRecAsProduct.Snd

      lazy val mu = Raw(Predef[RawMu](variable))
      lazy val fZeroMu = fZeroIn * mu
      
      lazy val fRec: Material[F[Fix[F]], ?] = f(recurse)(using next)
      lazy val fRecAsProduct: AsProduct[F[Nothing], ?, fRec.Raw] =
        fRec.asProduct(fZeroIn).get
          .asInstanceOf[AsProduct[F[Nothing], ?, fRec.Raw]] // should not be needed :(
      lazy val recurse: Material[Fix[F], ?] = Typed(
        fZeroMu.expr,
        raw => Fix(fRec.apply(fRecAsProduct.unapply(fZeroMu.apply(raw)): fRec.Raw)),
        fix => fZeroMu.unapply(fRecAsProduct.apply(fRec.unapply(fix.unfix)))
      )
      val muExpr = Raw(Mu(variable, fRecAsProduct.snd))
      val result = fZero * muExpr
      Typed(
        result.expr,
        raw => Fix(fRec.apply(fRecAsProduct.unapply(result.apply(raw)))),
        fix => result.unapply(fRecAsProduct.apply(fRec.unapply(fix.unfix)))
      )
