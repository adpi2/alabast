package alabast

import Comparison.{Greater, Lower, Equal}
import compiletime.ops.int._
import Auto._

sealed trait Expr[T]:
  type R = T
  val autos: LazyList[Auto[T]]

case object Zero extends Expr[Nothing]:
  val autos = LazyList()

case object One extends Expr[Unit]:
  val autos = LazyList(identity)

final case class Predef[T](variable: Variable) extends Expr[T]:
  val autos = LazyList(identity)

final case class Sum[A, B](left: Expr[A], right: Expr[B]) extends Expr[Either[A, B]]:
  val autos = for
    f <- left.autos
    g <- right.autos
  yield Iso.sum(f, g)

final case class Repeat[A](n: Int, expr: Expr[A]) extends Expr[(Int, A)]:
  val autos = {
    // val nAutos: Seq[Array[Auto[A]]] = 
    //   (0 until n)
    //     .foldLeft(Seq(List.empty[Auto[A]])) {
    //       (acc, _) =>
    //         for
    //           list <- acc
    //           auto <- expr.autos
    //         yield auto :: list
    //     }
    //     .map(_.toArray)
    
    for
      f <- permutations(n)
      auto <- expr.autos
    yield Auto[(Int, A)](
      (i, x) => (f.apply(i), auto.apply(x)),
      (i, x) => (f.unapply(i), auto.unapply(x))
    )
  }

final case class Product[A, B](fst: Expr[A], snd: Expr[B]) extends Expr[(A, B)]:
  val autos =
    for
      f <- fst.autos
      g <- snd.autos
    yield Iso.product(f, g)

final case class Mu[R](mu: Variable, expr: Expr[R]) extends Expr[R]:
  val autos: LazyList[Auto[R]] = expr.autos.map(this.fold(_))

object Expr:
  given Order[Expr[?]]:
    def compare(x: Expr[?], y: Expr[?]): Comparison = (x, y) match
      case (Sum(xLeft, xRight), Sum(yLeft, yRight)) => 
        compare(xLeft, yLeft).orElse(compare(xRight, yRight))
      case (Sum(xLeft, _), y) => compare(xLeft, y).orElse(Greater)
      case (x, Sum(yLeft, _)) => compare(x, yLeft).orElse(Lower)
      case (Repeat(m, x), Repeat(n, y)) => compare(x, y).orElse(order[Int].compare(m, n))
      case (Repeat(_, x), y) => compare(x, y).orElse(Greater)
      case (x, Repeat(_, y)) => compare(x, y).orElse(Lower)
      case (Product(xFst, xSnd), Product(yFst, ySnd)) =>
        compare(xFst, yFst).orElse(compare(xSnd, ySnd))
      case (Product(xFst, _), y) => compare(xFst, y).orElse(Greater)
      case (x, Product(yFst, _)) => compare(x, yFst).orElse(Lower)
      case (Mu(_, x), Mu(_, y)) => compare(x, y)
      case (Mu(_, _), _) => Greater
      case (_, Mu(_, _)) => Lower
      case (Predef(x), Predef(y)) => order[Int].compare(y.id, x.id)
      case (Predef(_), _) => Greater
      case (_, Predef(_)) => Lower
      case (One, One) => Equal
      case (One, Zero) => Greater
      case (Zero, One) => Lower
      case (Zero, Zero) => Equal

  extension [X, Y] (x: Expr[X])

    def + (y: Expr[Y]): Material[Either[X, Y], ?] = (x, y) match
      case (Zero, y) => Typed(y, Iso(Right[X, Y], _.right.get)) // 00
      case (x, Zero) => Typed(x, Iso(Left[X, Y], _ .left.get)) // 10
      case (Sum(xLeft, xRight), Sum(yLeft, yRight)) =>
        order.compare(xLeft.leader, yLeft.leader) match
          case Equal => // 20
            ((xLeft + yLeft) + (xRight + yRight)).imap {
              case Left(Left(x)) => Left(Left(x))
              case Left(Right(y)) => Right(Left(y))
              case Right(Left(x)) => Left(Right(x))
              case Right(Right(x)) => Right(Right(x))
            } {
              case Right(Right(x)) => Right(Right(x))
              case Right(Left(y)) => Left(Right(y))
              case Left(Right(x)) => Right(Left(x))
              case Left(Left(x)) => Left(Left(x))
            }
          case Greater => // 21
            sum(xLeft, xRight + y).imap {
              case Left(x) => Left(Left(x))
              case Right(Left(x)) => Left(Right(x))
              case Right(Right(y)) => Right(y)
            } {
              case Left(Left(x)) => Left(x)
              case Left(Right(x)) => Right(Left(x))
              case Right(y) => Right(Right(y))
            }
          case Lower => // 22
            sum(yLeft, x + yRight).imap {
              case Left(y) => Right(Left(y))
              case Right(Left(x)) => Left(x)
              case Right(Right(y)) => Right(Right(y))
            } {
              case Right(Left(y)) => Left(y)
              case Left(x) => Right(Left(x))
              case Right(Right(y)) => Right(Right(y))
            }
      case (Sum(left, right), _) => 
        order.compare(left.leader, y.leader) match
          case Equal => // 30
            ((left + y) + Raw(right)).imap {
              case Left(Left(x)) => Left(Left(x))
              case Left(Right(y)) => Right(y)
              case Right(x) => Left(Right(x))
            } {
              case Left(Left(x)) => Left(Left(x))
              case Right(y) => Left(Right(y))
              case Left(Right(x)) => Right(x)
            }
          case Greater => // 31
            sum(left, (right + y)).imap {
              case Left(x) => Left(Left(x))
              case Right(Left(x)) => Left(Right(x))
              case Right(Right(y)) => Right(y)
            } {
              case Left(Left(x)) => Left(x)
              case Left(Right(x)) => Right(Left(x))
              case Right(y) => Right(Right(y))
              case Left(_) => absurd // should not be needed
            }
          case Lower => // 32
            Typed(Sum(y, x), Iso(_.swap, _.swap))
      case (_, Sum(left, right)) =>
        order.compare(x.leader, left.leader) match
          case Equal => // 40
            ((x + left) + Raw(right)).imap {
              case Left(Left(x)) => Left(x)
              case Left(Right(y)) => Right(Left(y))
              case Right(y) => Right(Right(y))
            } {
              case Left(x) => Left(Left(x))
              case Right(Left(y)) => Left(Right(y))
              case Right(Right(y)) => Right(y)
            }
          case Greater => // 41
            Raw(Sum(x, y))
          case Lower => // 42
            sum(left, x + right).imap {
              case Left(y) => Right(Left(y))
              case Right(Left(x)) => Left(x)
              case Right(Right(y)) => Right(Right(y))
            } {
              case Right(Left(y)) => Left(y)
              case Left(x) => Right(Left(x))
              case Right(Right(y)) => Right(Right(y))
            } 
      case (x, y) =>
        order.compare(x.leader, y.leader) match
          case Equal => // 50
            Repeat(x.coeff + y.coeff, x.leader)
              .split(x.coeff)
              .asInstanceOf[Material[Either[X, Y], ?]]
          case Greater => Raw(Sum(x, y)) // 51
          case Lower => Typed(Sum(y, x), Iso(_.swap, _.swap)) // 52

    def * (y: Expr[Y]): Material[(X, Y), ?] = (x, y) match
      case (Zero, _) => zero // 00
      case (_, Zero) => zero // 10
      case (One, y) => Typed(y, Iso(((), _), _(1))) // 20
      case (x, One) => Typed(x, Iso((_, ()), _(0))) // 30
      case (Sum(left, right), y) => // 40
        (left * y + right * y).imap {
          case Left((x, y)) => (Left(x), y)
          case Right((x, y)) => (Right(x), y)
        }((x, y) => x.map((_, y)).left.map((_, y)))
      case (x, Sum(left, right)) => // 50
        (x * left + x * right).imap {
          case Left((x, y)) => (x, Left(y))
          case Right((x, y)) => (x, Right(y))
        } ((x, y) => y.map((x, _)).left.map((x, _)))
      case (Repeat(m, x), Repeat(n, y)) =>
        ((m * n) * (x * y)).imap
          { case (i, (x, y)) => ((i / n, x), (i % n, y)) }
          { case ((i, x), (j, y)) => (i * j, (x, y)) }
      case (Repeat(n, x), _) =>
        (n * (x * y)).imap
          { case (i, (x, y)) => ((i, x), y) }
          { case ((i, x), y) => (i, (x, y)) }
      case (_, Repeat(n, y)) =>
        (n * (x * y)).imap
          { case (i, (x, y)) => (x, (i, y)) }
          { case (x, (i, y)) => (i, (x, y)) }
      case (Product(xFst, xSnd), Product(yFst, ySnd)) =>
        if xFst > yFst then // 90
          product(xFst, xSnd * y).imap
            { case (x1, (x2, y)) => ((x1, x2), y) }
            { case ((x1, x2), y) => (x1, (x2, y)) }
        else // 91
          product(yFst, x * ySnd).imap 
            { case (y1, (x, y2)) => (x, (y1, y2)) }
            { case (x, (y1, y2)) => (y1, (x, y2)) }
      case (Product(fst, snd), y) =>
        if  fst > y then // A0
          product(fst, snd * y).imap
            { case (x1, (x2, y)) => ((x1, x2), y) }
            { case ((x1, x2), y) => (x1, (x2, y)) }
        else Typed(Product(y, x), Iso(_.swap, _.swap)) // A1
      case (x, Product(fst, snd)) =>
        if x > fst then Raw(Product(x, y)) // B0
        else //B1
          product(fst, x * snd).imap
            { case (y1, (x, y2)) => (x, (y1, y2)) }
            { case (x, (y1, y2)) => (y1, (x, y2)) }
      case (x, y) => 
        if x >= y then Raw(Product(x, y))
        else Typed(Product(y, x), Iso(_.swap, _.swap)) // C0
    
    def subtract(y: Expr[Y]): Option[Expr[?]] = (x, y) match
      case (x, Zero) => Some(x) // 00
      case (Sum(xLeft, xRight), Sum(yLeft, yRight)) =>
        order.compare(xLeft.leader, yLeft.leader) match
          case Equal => 
            for {
              left <- xLeft.subtract(yLeft) // 10
              right <- xRight.subtract(yRight) // 11
            } yield (left, right) match
              case (Zero, _) => right // 12
              case (_, Zero) => left // 13
              case _ => Sum(left, right) // 14
          case Greater =>
            xRight.subtract(y).map { //15
              case Zero => xLeft // 16
              case diff => Sum(xLeft, diff) // 17
            }
          case Lower => None // 18
      case (Sum(left, right), y) =>
        order.compare(left.leader, y.leader) match
          case Equal => 
            left.subtract(y).map { // 20
              case Zero => right // 21
              case left => Sum(left, right) // 22
            } 
          case Greater => 
            right.subtract(y).map { // 23
              case Zero => left // 24
              case diff => Sum(left, diff) //25
            }
          case Lower => None // 26
      case (x, Sum(left, right)) => None
      case (x, y) =>
        order.compare(x.leader, y.leader) match
          case Equal =>
            x.coeff - y.coeff match
              case 0 => Some(Zero) // 30
              case 1 => Some(x.leader) // 31
              case n if n > 1 => Some(Repeat(n, x.leader)) // 32
              case _ => None
          case _ => None // 33

    // def factor(div: Expr[Y]): Option[Expr[?]] = (x, div) match
    //   case (Zero, _) => Some(Zero) // 00
    //   case (x, One) => Some(x) // 10
    //   case (Sum(left, right), Sum(divLeft, divRight)) =>
    //     for
    //       leftQuotient <- left.factor(divLeft) // 20
    //       rightFactor = (divRight * leftQuotient).expr
    //       remainder <- right.subtract(rightFactor) // 21
    //       rightQuotient <- remainder.factor(div) // 22
    //     yield rightQuotient match
    //       case Zero => leftQuotient //23
    //       case rightQuotient => Sum(leftQuotient, rightQuotient) //24
    //   case (Sum(left, right), div) =>
    //     for
    //       leftQuotient <- left.factor(div)
    //       rightQuotient <- right.factor(div)
    //     yield Sum(leftQuotient, rightQuotient)
    //   case (_, Sum) => None
    //   case (Product(fst, snd), Product(fstDiv, sndDiv)) =>
    //     order.compare(fst, fstDiv) match
    //       case Equal => snd.factor(sndDiv)
    //       case Greater => snd.factor(div).map(factor => (fst * factor).expr)
    //       case Lower => None
    //   case (Product(fst, snd), div) =>
    //     if fst == div then Some(snd)
    //     else snd.factor(div).map(factor => (fst * factor).expr)
    //   case (_, Product(_, _)) => None
    //   case (x, div) => if x == div then Some(One) else None

    def asProduct(y: Expr[Y]): Option[AsProduct[Y, ?, X]] =
      (x, y) match
        case (Zero, _) => Some(AsProduct(zero, Zero)) // 00
        case (_, One) => Some( // 10
          AsProduct(Typed(x, Iso((x => ((), x)), ((_, x) => x))), x)
        )
        case (Sum(xLeft, xRight), Sum(yLeft, yRight)) =>
          xLeft.asProduct(yLeft).flatMap { leftLeftAsProduct => // 20
            val leftRight: Material[(yRight.R, leftLeftAsProduct.Snd), ?] = Raw(yRight) * Raw(leftLeftAsProduct.snd)
            for
              remainder <- xRight.subtract(leftRight.expr) // 21
              rightAsProduct <- remainder.asProduct(y) // 22
            yield // 23 // 24
              val leftUnderlying: Material[(Y, leftLeftAsProduct.Snd), ?] = 
                (leftLeftAsProduct.underlying + leftRight)
                  .imap {
                    case Left((y, x)) => (Left(y), x)
                    case Right((y, x)) => (Right(y), x)
                  } { (y, x) => y.map((_, x)).left.map((_, x)) }
              val leftAsProduct =
                AsProduct(
                  leftUnderlying.withRaw[xLeft.R],
                  leftLeftAsProduct.snd
                )
              sumAsProduct(leftAsProduct, rightAsProduct)
          }
        case (Sum(left, right), y) =>
          for
            leftProduct <- left.asProduct(y) // 30
            rightProduct <- right.asProduct(y) // 31
          yield // 32
            val underlying : Material[(Y, Either[leftProduct.Snd, rightProduct.Snd]), ?] =
                (leftProduct.underlying + rightProduct.underlying).imap {
                  case Left((y, x)) => (y, Left(x))
                  case Right((y, x)) => (y, Right(x))
                } { (y, x) =>  x.map((y, _)).left.map((y, _)) }
            // cannot prove that (left + right).R =:= X
            AsProduct(underlying.withRaw[X], Sum(leftProduct.snd, rightProduct.snd))  
        case (_, Sum(_, _)) => None // 40
        case (Repeat(m, x), Repeat(n, y)) =>
          if (m % n == 0)
            for (leader <- x.asProduct(y)) // 50
            yield
              (m / n) match
                case 1 => // 51
                  val underlying = (m * leader.underlying).imap
                    { case (i, (y, x)) => ((i , y), x) }
                    { case ((i, y), x) => (i, (y, x)) }
                  AsProduct(underlying.withRaw[X], leader.snd)
                case k => // 52
                  val underlying = (m * leader.underlying).imap
                    { case (i, (y, x)) => ((i % n, y), (i / n, x)) }
                    { case ((i, y), (j, x)) => (j * n + i, (y, x)) }
                  AsProduct(underlying.withRaw[X], Repeat(k, leader.snd))
          else None // 53
        case (Repeat(n, x), _) =>
          for (leader <- x.asProduct(y)) // 60
          yield // 61
            val underlying = (n * leader.underlying).imap
              { case (i, (y, x)) => (y, (i, x)) }
              { case (y, (i, x)) => (i, (y, x)) }
            AsProduct(underlying.withRaw[X], Repeat(n, leader.snd))
        case (_, Repeat(_, _)) => None
        case (Product(xFst, xSnd), Product(yFst, ySnd)) =>
          order.compare(xFst, yFst) match
            case Equal => 
              for sndProduct <- xSnd.asProduct(ySnd) // 80
              yield // 81
                val underlying = 
                  product(yFst, sndProduct.underlying).imap 
                    { case (fst, (snd, x)) => ((fst, snd), x) }
                    { case ((fst, snd), x) => (fst, (snd, x)) }
                // cannot prove that (fst * snd).R =:= X
                AsProduct(underlying.withRaw[X], sndProduct.snd)
            case Greater => 
              for sndProduct <- xSnd.asProduct(y) // 82
              yield productAsProduct(xFst, sndProduct) // 83
            case Lower => None // 84

        case (Product(`y`, snd), _) =>
          Some(AsProduct(Raw(Product(y, snd)), snd)) // 90
        case (Product(fst, snd), _) =>
          for sndProduct <- snd.asProduct(y) // 91
          yield productAsProduct(fst, sndProduct)
        case (_, Product(_, _)) => None // A0
        case (`y`, _) =>
          val underlying = Raw(x).imap { (_, ()) } { _(0) } 
          Some(AsProduct(underlying, One))
        case _ => None

  def repeat[X](coeff: Int, x: Expr[X]): Material[(Int, X), ?] = x match
    case Sum(left, right) =>
      (repeat(coeff, left) + repeat(coeff, right)).imap {
        case Left((i, x)) => (i, Left(x))
        case Right((i, x)) => (i, Right(x))
      } {
        (i, x) => x.left.map((i, _)).map((i, _))
      }
    case Repeat(n, x) => 
      Typed(
        Repeat(coeff * n, x),
        Iso(
          (i, x) => (i / n, (i % n, x)),
          { case (i, (j, x)) => (i * n + j, x) }
        )
      )
    case _ => Raw(Repeat(coeff, x))


    extension [X] (x: Expr[X])
    def show: String = x match
      case Zero => "zero" // 0
      case One => "one"
      case Predef(v) => v.name
      case Sum(left, right) => s"${left.show} + ${right.show}"
      case Repeat(n, expr) => s"$n * ${expr.show}"
      case Product(fst, snd) => s"${fst.show} * ${snd.show}"
      case Mu(mu, unmu) => s"mu(${mu.name} => ${unmu.show})"

    def leader: Expr[?] = x match
      case Sum(left, _) => left.leader
      case Repeat(_, x) => x
      case _ => x
    
    def coeff: Int = x match
      case Sum(x, _) => x.coeff
      case Repeat(coeff, _) => coeff
      case _ => 1

    def autoMap(v: Variable, f: Iso[?, ?]): Auto[X] = x match
      case Zero => Auto.identity
      case One => Auto.identity
      case Predef(`v`) => f.asInstanceOf[Auto[X]]
      case Predef(_) => Auto.identity
      case Sum(left, right) => Iso.sum(left.autoMap(v, f), right.autoMap(v, f))
      case Repeat(_, x) => Iso.product(Auto.identity[Int], x.autoMap(v, f))
      case Product(fst, snd) => Iso.product(fst.autoMap(v, f), snd.autoMap(v, f))
      case x@ Mu(_, expr) => x.fold(expr.autoMap(v, f))
    
    def contains(v: Variable): Boolean = x match
      case Zero => false
      case One => false
      case Predef(`v`) => true
      case Predef(_) => false
      case Sum(left, right) => left.contains(v) || right.contains(v)
      case Repeat(_, x) => x.contains(v)
      case Product(fst, snd) => fst.contains(v) || snd.contains(v)
      case Mu(_, _) => false // MAYBE expr.contains(v)...

    def map(mapping: Map[Variable, Variable])(using Context): Material[X, ?] = x match
      case Zero => Raw(Zero)
      case One => Raw(One)
      case Predef(x) if mapping.contains(x) => Raw(Predef(mapping(x)))
      case Predef(_) => Raw(x)
      case Sum(left, right) => left.map(mapping) + right.map(mapping)
      case Repeat(n, x) => n * x.map(mapping)
      case Product(fst, snd) => fst.map(mapping) * snd.map(mapping)
      case Mu(x, expr) if mapping.contains(x) => Raw(Predef(mapping(x)))
      case Mu(x, expr) => Context.in(y => mu(y, expr.map(mapping + (x -> y))))

  extension [X] (x: Mu[X])
    def fold(f: Auto[X]): Auto[X] =
      val Mu(mu, unmu) = x
      lazy val iso: Auto[X] = f.andThen(Iso.lazily(fold))
      lazy val fold: Auto[X] = unmu.autoMap(mu, iso)
      iso

    def unmu(using Context): Material[X, ?] =
      val Mu(x0, unmu) = x
      def unwrap[Y](y: Expr[Y], mapping: Map[Variable, Variable])(using Context): Material[Y, ?] = y match
        case Zero => Raw(Zero)
        case One => Raw(One)
        case Predef(`x0`) => 
          Context.in { x1 =>
            mu(x1, unmu.map(mapping + (x0 -> x1)).asInstanceOf[Material[Y, ?]])
          }
        case Predef(x1) if mapping.contains(x1) => Raw(Predef(mapping(x1)))
        case Predef(_) => Raw(y)
        case Sum(left, right) => unwrap(left, mapping) + unwrap(right, mapping)
        case Repeat(n, y) => n * unwrap(y, mapping)
        case Product(fst, snd) => unwrap(fst, mapping) * unwrap(snd, mapping)
        case Mu(x1, expr) =>
          Context.in(x2 => mu(x2, unwrap(expr, mapping + (x1 -> x2))))
      unwrap(unmu, Map())
  
  extension [X] (x: Repeat[X])
    private def split(n: Int): Material[Either[?, ?], ?] = 
      (n, x.coeff - n) match
        case (1, 1) =>
          Typed[Either[X, X], (Int, X)](
            x,
            Iso(
              (i, x) => if (i == 0) Left(x) else Right(x), 
              {
                case Left(x) => (0, x)
                case Right(x) => (1, x)
              }
            )
          ).asInstanceOf[Material[Either[?, ?], ?]]
        case (1, _) => 
          Typed[Either[X, (Int, X)], (Int, X)](
            x,
            Iso(
              (i, x) => if (i == 0) Left(x) else Right((i - 1, x)),
              {
                case Left(x) => (0, x)
                case Right((i, x)) => (i + 1, x)
              }
            )
          ).asInstanceOf[Material[Either[?, ?], ?]]
        case (_, 1) =>
          Typed[Either[(Int, X), X], (Int, X)](
            x,
            Iso(
              (i, x) => if (i < n) Left((i, x)) else Right(x),
              {
                case Left((i, x)) => (i, x)
                case Right(x) => (n, x)
              }
            )
          ).asInstanceOf[Material[Either[?, ?], ?]]
        case (_, _) =>
          Typed[Either[(Int, X), (Int, X)], (Int, X)](
            x,
            Iso(
              (i, x) => if (i < n) Left((i, x)) else Right((i - n, x)),
              {
                case Left((i, x)) => (i, x)
                case Right((i, x)) => (i + n, x)
              }
            )
          ).asInstanceOf[Material[Either[?, ?], ?]]

  private def sum[X, Y](x: Expr[X], y: Material[Y, ?]): Material[Either[X, Y], ?] = y match
    case Raw(y) => Raw(Sum(x, y))
    case Typed(expr, cons) => Typed(Sum(x, expr), Iso(_.map(cons.apply), _.map(cons.unapply)))

  private def product[X, Y](x: Expr[X], y: Material[Y, ?]): Material[(X, Y), ?] = y match
    case Raw(y) => Raw(Product(x, y))
    case Typed(expr, cons) =>  
      Typed(Product(x, expr), Iso((x, y) => (x, cons.apply(y)), (x, y) => (x, cons.unapply(y))))

  private def productAsProduct[X, Y, Z](fst: Expr[?], asProduct: AsProduct[Y, Z, ?]): AsProduct[Y, ?, X] =
    asProduct.snd match
      case One => // 62
        val underlying = product(fst, asProduct.underlying)
          .imap
            { case (fst, (y, ())) => (y, fst) }
            { case (y, fst) => (fst, (y, ())) }
        AsProduct(underlying.withRaw[X], fst)
      case snd => 
        val underlying = product(fst, asProduct.underlying).imap
          { case (fst, (y, snd)) => (y, (fst, snd)) }
          { case (y, (fst, snd)) => (fst, (y, snd)) }
        AsProduct(underlying.withRaw[X], Product(fst, snd))
  
  private def sumAsProduct[X, Y, Z1, Z2](left: AsProduct[Y, Z1, ?], right: AsProduct[Y, Z2, ?]): AsProduct[Y, ?, X] =
    right.snd match
      case Zero =>
        AsProduct(left.underlying.withRaw[X], left.snd)
      case _ =>
        val underlying: Material[(Y, Either[Z1, Z2]), ?] =
          (left.underlying + right.underlying).imap {
            case Left((y, x)) => (y, Left(x))
            case Right((y, x)) => (y, Right(x))
          } { (y, x) => x.map((y, _)).left.map((y, _)) }
        AsProduct(underlying.withRaw[X], Sum(left.snd, right.snd))
