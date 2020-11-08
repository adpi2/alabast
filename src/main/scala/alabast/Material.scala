package alabast

import Comparison._
import Expr._

sealed trait Material[T, R]:
  type Raw = R
  val expr: Expr[R]
  val cons: Iso[R, T]
  val isos: LazyList[Iso[R, T]]
  val autos: LazyList[Auto[T]]
  // unsafe cast R to U
  def withRaw[U]: Material[T, U] = asInstanceOf[Material[T, U]]

final case class Raw[T](expr: Expr[T]) extends Material[T, T]:
  override val cons: Auto[T] = Auto.identity
  override val autos: LazyList[Auto[T]] = expr.autos
  override val isos: LazyList[Auto[T]] = autos

final case class Typed[T, R](val expr: Expr[R], val cons: Iso[R, T]) extends Material[T, R]:
  override val isos: LazyList[Iso[R, T]] = expr.autos.map(_.andThen(cons))
  override val autos: LazyList[Auto[T]] = expr.autos.map(cons.invert.andThen(_).andThen(cons))

def zero[T]: Material[T, Nothing] = Typed(Zero, Iso.absurd)
def one: Material[Unit, Unit] = Raw(One)
def predef[T](name: String)(using ctx: Context): Material[T, T] = Raw(Predef[T](ctx.variables(name)))
def mu[F[_], T](f: Material[Any, ?] => Context ?=> Material[F[Any], ?])(fix: Iso[F[T], T])(using ctx: Context): Material[T, ?] =
  Expr.mu[F, T]([X] => (x: Material[X, ?]) => (using ctx: Context) => f(x.asInstanceOf[Material[Any, ?]]).asInstanceOf[Material[F[X], ?]])(fix)

object Material:
  given Order[Material[?, ?]]:
    def compare(x: Material[?, ?], y: Material[?, ?]) =
      order[Expr[?]].compare(x.expr, y.expr)

  extension [X, R, Y] (x: Material[X, R])
    def show: String = x.expr.show

    def imap(f: X => Y)(g: Y => X): Typed[Y, R] = x match
      case Raw(expr) => Typed(expr, Iso(f, g))
      case Typed(expr, cons) => Typed(expr, cons.andThen(Iso(f, g)))
    
    def imap(iso: Iso[X, Y]): Typed[Y, R] = x match
      case Raw(expr) => Typed(expr, iso)
      case Typed(expr, cons) => Typed(expr, cons.andThen(iso))

    def + (y: Material[Y, ?]): Material[Either[X, Y], ?] = (x, y) match
      case (Raw(x), Raw(y)) => x + y
      case (Raw(x), Typed(y, cons)) => (x + y).imap(_.map(cons.apply))(_.map(cons.unapply))
      case (Typed(x, cons), Raw(y)) => (x + y).imap(_.left.map(cons.apply))(_.left.map(cons.unapply))
      case (Typed(x, xCons), Typed(y, yCons)) => (x + y).imap
        { _.map(yCons.apply).left.map(xCons.apply) }
        { _.map(yCons.unapply).left.map(xCons.unapply) }
    
    def * (y: Material[Y, ?]): Material[(X, Y), ?] with { type R <: Any } = (x, y) match
      case (Raw(x), Raw(y)) => x * y
      case (Raw(x), Typed(y, cons)) =>
        (x * y).imap
          { (x, y) => (x, cons.apply(y)) }
          { (x, y) => (x, cons.unapply(y)) }
      case (Typed(x, cons), Raw(y)) =>
        (x * y).imap
          { (x, y) => (cons.apply(x), y) }
          { (x, y) => (cons.unapply(x), y) }
      case (Typed(x, xCons), Typed(y, yCons)) => 
        (x * y).imap
          { (x, y) => (xCons.apply(x), yCons.apply(y)) }
          { (x, y) => (xCons.unapply(x), yCons.unapply(y)) }
    
    def asProduct(y: Material[Y, ?]): Option[AsProduct[Y, ?, R]] = y match
      case Raw(y) => x.expr.asProduct(y)
      case Typed(expr, cons) =>
        for product <- x.expr.asProduct(expr)
        yield
          AsProduct(
            product.underlying.imap
              { (y, x) => (cons.apply(y), x) }
              { (y, x) => (cons.unapply(y), x) },
            product.snd
          )
    
    def as(y: Material[Y, ?]): Seq[Iso[X, Y]] =
      if x.expr == y.expr then
        val cons = y.withRaw[R].cons
        x.isos.map(f => f.invert.andThen(cons))
      else Seq.empty
  
  extension [X, R] (x: Material[X, R])
    def ^(pow: Int): Material[List[X], ?] = x match
      case Raw(x) => x ^ pow
      case Typed(x, cons) => (x ^ pow).imap
        { case xs => xs.map(cons.apply) }
        { case xs => xs.map(cons.unapply) }
       
    def unmu(using Context): Material[X, ?] = x match
      case Raw(x @ Mu(_, _)) => x.unmu
      case Typed(x @ Mu(_, _), cons) => x.unmu.imap(cons) 
      case _ => absurd

  extension [X, R] (n: Int)
    def * (x: Material[X, R]): Material[(Int, X), ?] = x match
      case Raw(x) => repeat(n, x)
      case Typed(x, cons) => repeat(n, x).imap((i, x) => (i, cons.apply(x)))((i, x) => (i, cons.unapply(x)))
 
