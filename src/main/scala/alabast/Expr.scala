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
  val autos =
    val tuples = expr.autos.tuples(n)
    for
      f <- permutations(n)
      tuple <- tuples
    yield Auto[(Int, A)](
      (i, x) => (f.apply(i), tuple(i).apply(x)),
      (i, x) => (f.unapply(i), tuple(i).unapply(x))
    )

final case class Product[A, B](fst: Expr[A], snd: Expr[B]) extends Expr[(A, B)]:
  val autos =
    for
      f <- fst.autos
      g <- snd.autos
    yield Iso.product(f, g)

final case class Power[A](n: Int, expr: Expr[A]) extends Expr[List[A]]:
  val autos =
    val tuples = expr.autos.tuples(n)
    for
      f <- permutations(n)
      tuple <- tuples
    yield Auto[List[A]](
      x => x.zip(tuple).map((x, f) => f.apply(x)),
      x => x.zip(tuple).map((x, f) => f.unapply(x))
    )

final case class Mu[R](mu: Variable, expr: Expr[R]) extends Expr[R]:
  val autos: LazyList[Auto[R]] = expr.autos.map(this.fold(_))

object Expr:
  given Order[Expr[?]]:
    def compare(x: Expr[?], y: Expr[?]): Comparison = (x, y) match
      case (Sum(xLeft, xRight), Sum(yLeft, yRight)) => 
        compare(xLeft, yLeft) // 00
          .orElse(compare(xRight, yRight)) // 01
      case (Sum(xLeft, _), y) =>
        compare(xLeft, y) // 10
          .orElse(Greater) // 11
      case (x, Sum(yLeft, _)) =>
        compare(x, yLeft) // 20
          .orElse(Lower) // 21
      case (Repeat(m, x), Repeat(n, y)) =>
        compare(x, y) // 30
          .orElse(order[Int].compare(m, n)) // 31
      case (Repeat(_, x), y) =>
        compare(x, y) // 40
          .orElse(Greater) // 41
      case (x, Repeat(_, y)) =>
        compare(x, y) // 50
          .orElse(Lower) // 51
      case (Product(xFst, xSnd), Product(yFst, ySnd)) =>
        compare(xFst, yFst) // 60
          .orElse(compare(xSnd, ySnd)) // 61
      case (Product(xFst, _), y) =>
        compare(xFst, y) // 70
          .orElse(Greater) // 71
      case (x, Product(yFst, _)) =>
        compare(x, yFst) // 80
          .orElse(Lower) // 81
      case (Power(m, x), Power(n, y)) =>
        compare(x, y) // 90
          .orElse(order[Int].compare(m, n)) // 91
      case (Power(_, x), y) => 
        compare(x, y) // A0
          .orElse(Greater) // A1
      case (x, Power(_, y)) => compare(x, y).orElse(Lower)
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

  extension [X] (x: Expr[X])
    def show: String = x match
      case Zero => "zero" // 0
      case One => "one"
      case Predef(v) => v.name
      case Sum(left, right) => s"${left.show} + ${right.show}"
      case Repeat(n, expr) => s"$n * ${expr.show}"
      case Product(fst, snd) => s"${fst.show} * ${snd.show}"
      case Power(n, x) => s"${x.show}^$n"
      case Mu(mu, unmu) => s"mu(${mu.name} => ${unmu.show})"

    def ^(pow: Int): Material[List[X], ?] = x match
      case Zero => zero // 00
      case One => // 10
        Typed(One, Iso(_ => List.fill(pow)(()), _ => ()))
      case Sum(_, _) => // 20
        Iterator
          .iterate(
            Typed(x, Iso(x => List(x), xs => xs.head))
              .asInstanceOf[Material[List[X], ?]]
            ) { y =>
              (Raw(x) * y).imap
                { (x, y) => x :: y }
                { xs => (xs.head, xs.tail) }
            }
          .drop(pow - 1).next
      case Repeat(n, x) => // 30
        val powers: LazyList[Int] = LazyList.iterate(n)(p => n * p)
        (math.pow(n.toDouble, pow.toDouble).intValue * (x ^ pow)).imap
          { (i, xs) => xs.zip(powers).map((x, k) => ((i / k) % n, x)) }
          { xs =>
            xs.foldRight((0, List.empty[x.R])) {
              case ((i, x), (j, xs)) => (i + j * n, x :: xs)
            }
          }
      case Product(fst, snd) => // 40
        ((fst ^ pow) * (snd ^ pow)).imap{ (xs, ys) => xs.zip(ys) } { xs => xs.unzip }
      case Power(n, x) => // 50
        Typed(
          Power(n * pow, x),
          Iso(
            xs => xs.grouped(n).toList,
            xs => xs.flatten[x.R]
          )
        )
      case _ => Raw(Power(pow, x))

    def leader: Expr[?] = x match
      case Sum(left, _) => left.leader
      case Repeat(_, x) => x
      case _ => x

    def base: Expr[?] = x match
      case Sum(_, _) | Repeat(_, _) => absurd
      case Product(fst, _) => fst.base
      case Power(_, x) => x
      case _ => x
    
    def coeff: Int = x match
      case Sum(_, _) => absurd
      case Repeat(coeff, _) => coeff
      case _ => 1

    def power: Int = x match
      case Product(_, _) | Sum(_, _) | Repeat(_, _) => absurd
      case Power(power, _) => power
      case _ => 1      

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
      case (Repeat(m, x), Repeat(n, y)) => // 60
        ((m * n) * (x * y)).imap
          { case (i, (x, y)) => ((i / n, x), (i % n, y)) }
          { case ((i, x), (j, y)) => (i * j, (x, y)) }
      case (Repeat(n, x), _) => // 70
        (n * (x * y)).imap
          { case (i, (x, y)) => ((i, x), y) }
          { case ((i, x), y) => (i, (x, y)) }
      case (_, Repeat(n, y)) => // 80
        (n * (x * y)).imap
          { case (i, (x, y)) => (x, (i, y)) }
          { case (x, (i, y)) => (i, (x, y)) }
      case (Product(xFst, xSnd), Product(yFst, ySnd)) =>
        order.compare(xFst.base, yFst.base) match
          case Equal => // 90
            ((xFst * yFst) * (xSnd * ySnd)).imap
              { case ((x1, y1), (x2, y2)) => ((x1, x2), (y1, y2)) }
              { case ((x1, x2), (y1, y2)) => ((x1, y1), (x2, y2)) }
          case Greater => // 91
            product(xFst, xSnd * y).imap
              { case (x1, (x2, y)) => ((x1, x2), y) }
              { case ((x1, x2), y) => (x1, (x2, y)) }
          case Lower => // 92
            product(yFst, x * ySnd).imap 
              { case (y1, (x, y2)) => (x, (y1, y2)) }
              { case (x, (y1, y2)) => (y1, (x, y2)) }
      case (Product(fst, snd), y) =>
        order.compare(fst.base, y.base) match
          case Equal => // A0
            ((fst * y) * Raw(snd)).imap
              { case ((x1, y), x2) => ((x1, x2), y) }
              { case ((x1, x2), y) => ((x1, y), x2) }
          case Greater => // A1
            product(fst, snd * y).imap
              { case (x1, (x2, y)) => ((x1, x2), y) }
              { case ((x1, x2), y) => (x1, (x2, y)) }
          case Lower => // A2
            Typed(Product(y, x), Iso(_.swap, _.swap))
      case (x, Product(fst, snd)) =>
        order.compare(x.base, fst.base) match
          case Equal => // B0
            ((x * fst) * Raw(snd)).imap
              { case ((x, y1), y2) => (x, (y1, y2)) }
              { case (x, (y1, y2)) => ((x, y1), y2) }
          case Greater => Raw(Product(x, y)) // B1
          case Lower => //B2
            product(fst, x * snd).imap
              { case (y1, (x, y2)) => (x, (y1, y2)) }
              { case (x, (y1, y2)) => (y1, (x, y2)) }
      case (x, y) =>
        order.compare(x.base, y.base) match
          case Equal => // C0
            Power(x.power + y.power, x.base)
              .split(x.coeff)
              .asInstanceOf[Material[(X, Y), ?]]
          case Greater => Raw(Product(x, y))
          case Lower => // C1
            Typed(Product(y, x), Iso(_.swap, _.swap))

    def asTermOf(y: Expr[Y]): Seq[X => Y] = (x, y) match
      case (_, Zero) => Seq.empty // 00
      case (Sum(xLeft, xRight), Sum(yLeft, yRight)) =>
        order.compare(xLeft.leader, yLeft.leader) match
          case Equal =>
            for
              left <- xLeft.asTermOf(yLeft) // 10
              right <- xRight.asTermOf(yRight) // 11
            yield _.left.map(left).map(right) // 12
          case Greater => Seq.empty // 13
          case Lower => 
            x.asTermOf(yRight).map(f => f.andThen(Right(_))) // 14, 15
      case (Sum(left, right), y) => Seq.empty // 20
      case (x, Sum(yLeft, yRight)) =>
        order.compare(x.leader, yLeft.leader) match
          case Equal =>
            x.asTermOf(yLeft).map(f => f.andThen(Left(_))) // 30, 31
          case Greater => Seq.empty // 32
          case Lower =>
            x.asTermOf(yRight).map(f => f.andThen(Right(_))) // 33, 34
      case (x, y) =>
        order.compare(x.leader, y.leader) match
          case Equal =>
            (x.coeff, y.coeff) match
              case(k, n) if (k == n) => x.autos.map(_.apply.asInstanceOf[X => Y]) // 40
              case (1, k) => // 41
                for
                  i <- 0 until k
                  apply <- x.autos.map(_.apply)
                yield apply.andThen((i, _)).asInstanceOf[X => Y]
              case (k, n) if n > k => // 42
                val leader = x.leader
                val tuples = leader.autos.map(_.apply).tuples(k)
                for
                  variation <- variations(k, n) 
                  tuple <- tuples
                yield { (x: (Int, leader.R)) => x match
                  case (i, r) => (variation(i), tuple(i)(r)) 
                }.asInstanceOf[X => Y]
              case _ => Seq.empty // 43
          case _ => Seq.empty // 44
    
    def subtract(y: Expr[Y]): Option[Expr[?]] = (x, y) match
      case (_, Zero) => Some(x) // 00
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
            xRight.subtract(y).map { // 15
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
              rightAsProduct.snd match
                case Zero =>
                  AsProduct(leftAsProduct.underlying.withRaw[X], leftAsProduct.snd)
                case _ =>
                  val underlying: Material[(Y, Either[leftAsProduct.Snd, rightAsProduct.Snd]), ?] =
                    (leftAsProduct.underlying + rightAsProduct.underlying).imap {
                      case Left((y, x)) => (y, Left(x))
                      case Right((y, x)) => (y, Right(x))
                    } { (y, x) => x.map((y, _)).left.map((y, _)) }
                  AsProduct(underlying.withRaw[X], Sum(leftAsProduct.snd, rightAsProduct.snd))
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
          order.compare(xFst.base, yFst.base) match
            case Equal => 
              for
                fst <- xFst.asProduct(yFst) // 80
                snd <- xSnd.asProduct(ySnd) // 81
              yield
                (fst.snd, snd.snd) match
                  case (One, _) => // 82
                    val underlying = product(yFst, snd.underlying).imap
                      { case (y1, (y2, x)) => ((y1, y2), x) }
                      { case ((y1, y2), x) => (y1, (y2, x)) }
                    AsProduct(underlying.withRaw[X], snd.snd)
                  case (_, One) => // 83
                    val underlying = (fst.underlying * Raw(ySnd)).imap
                      { case ((y1, x), y2) => ((y1, y2), x) }
                      { case ((y1, y2), x) => ((y1, x), y2) }
                    AsProduct(underlying.withRaw[X], fst.snd)
                  case _ => // 84
                    val underlying = 
                      (fst.underlying * snd.underlying).imap 
                        { case ((y1, x1), (y2, x2)) => ((y1, y2), (x1, x2)) }
                        { case ((y1, y2), (x1, x2)) => ((y1, x1), (y2, x2)) }
                    // cannot prove that (fst * snd).R =:= X
                    AsProduct(underlying.withRaw[X], Product(fst.snd, snd.snd))
            case Greater => 
              for sndProduct <- xSnd.asProduct(y) // 85
              yield productAsProduct(xFst, sndProduct) // 86
            case Lower => None // 87
        case (Product(xFst, xSnd), _) =>
          order.compare(xFst.base, y.base) match
            case Equal =>
              for
                fst <- xFst.asProduct(y)
              yield fst.snd match
                case One => // 90
                  AsProduct(Raw(Product(y, xSnd)).withRaw[X], xSnd)
                case _ => // 91
                  val underlying = (fst.underlying * Raw(xSnd)).imap
                    { case ((y, x1), x2) => (y, (x1, x2)) }
                    { case (y, (x1, x2)) => ((y, x1), x2) }
                  AsProduct(underlying.withRaw[X], Product(fst.snd, xSnd))
            case Greater =>
              for sndProduct <- xSnd.asProduct(y) // 92
              yield productAsProduct(xFst, sndProduct) // 93
            case Lower => None // 94
        case (_, Product(_, _)) => None // A0
        case (_, _) =>
          order.compare(x.base, y.base) match
            case Equal =>
              (x.power - y.power) match
                case 0 => // B0
                  val underlying = Raw(y).imap { (_, ()) } { _(0) }
                  Some(AsProduct(underlying.withRaw[X], One))
                case 1 => // B1
                  val snd = y.base
                  Some(AsProduct((y * snd).withRaw[X], snd))
                case pow if pow > 0 => // B2
                  val snd = Power(pow, y.base)
                  Some(AsProduct((y * snd).withRaw[X], snd))
                case _ => None // B3
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

  def mu[F[_], X](f: [X] => Material[X, ?] => Context ?=> Material[F[X], ?])(fix: Iso[F[X], X])(using ctx: Context): Material[X, ?] =
    val fZero = f(zero[X])
    val fOne = f(one).expr
    fZero.expr match
      case Zero => zero // 00
      case `fOne` => fZero.imap(fix) // 10
      case One => // 20
        Context.in { x => 
          lazy val recurse: Material[X, ?] = Typed(Predef[unmu.Raw](x),Iso.lazily(unmu.cons))
          lazy val unmu: Material[X, ?] = f(recurse).imap(fix)
          Typed(Mu(x, unmu.expr), unmu.cons)
        }
      
      case _ => // 30
        Context.in { x =>
          val fZeroIn = f(zero[X])
          lazy val recurse: Material[X, ?] = Typed(Predef[unmu.Raw](x),Iso.lazily(unmu.cons))
          lazy val unmu: Material[X, ?] = f(recurse).imap(fix)

          unmu.expr.subtract(fZeroIn.expr).flatMap(_.asProduct(Predef(x))) match
            case None => Typed(Mu(x, unmu.expr), unmu.cons)
            case Some(_) =>
              val mu = Raw(Predef[fRecAsProduct.Snd](x))
              val fZeroMu = fZeroIn * mu
              
              lazy val fRec: Material[F[X], ?] = f(recurse)
              lazy val fRecAsProduct: AsProduct[F[X], ?, fRec.Raw] =
                fRec.asProduct(fZeroIn).get
                  .asInstanceOf[AsProduct[F[X], ?, fRec.Raw]] // should not be needed :(
              lazy val recurse: Material[X, ?] = Typed(
                fZeroMu.expr,
                fZeroMu.cons
                  .andThen(Iso.lazily(fRecAsProduct.cons.invert))
                  .andThen(Iso.lazily(fRec.cons))
                  .andThen(fix)
              )
              val muExpr = Raw(Mu(x, fRecAsProduct.snd))
              val result = fZero * muExpr
              Typed(
                result.expr,
                result.cons
                  .andThen(fRecAsProduct.cons.invert)
                  .andThen(fRec.cons)
                  .andThen(fix)
              )
          }

  extension [X] (x: Mu[X])
    def fold(f: Auto[X]): Auto[X] =
      val Mu(mu, unmu) = x
      lazy val fold: Auto[X] = f.andThen(algebra(unmu))
      def algebra[Y](y: Expr[Y]): Auto[Y] = y match
        case Zero => Auto.identity
        case One => Auto.identity
        case Predef(`mu`) => Iso.lazily(fold.asInstanceOf[Auto[Y]])
        case Predef(_) => Auto.identity
        case Sum(left, right) => Iso.sum(algebra(left), algebra(right))
        case Repeat(_, y) => Iso.product(Auto.identity[Int], algebra(y))
        case Product(fst, snd) => Iso.product(algebra(fst), algebra(snd))
        case x@ Mu(_, expr) => x.fold(algebra(expr))
      fold

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
    private def split(n: Int): Material[? <: Either[Any, Any], (Int, X)] = 
      (n, x.coeff - n) match
        case (1, 1) =>
          Typed(x,
            Iso((i, x) => if (i == 0) Left(x) else Right(x), {
              case Left(x) => (0, x)
              case Right(x) => (1, x)
            })
          )
        case (1, _) => 
          Typed(x,
            Iso((i, x) => if (i == 0) Left(x) else Right((i - 1, x)), {
              case Left(x) => (0, x)
              case Right((i, x)) => (i + 1, x)
            })
          )
        case (_, 1) =>
          Typed(x,
            Iso((i, x) => if (i < n) Left((i, x)) else Right(x), {
              case Left((i, x)) => (i, x)
              case Right(x) => (n, x)
            })
          )
        case (_, _) =>
          Typed(x,
            Iso((i, x) => if (i < n) Left((i, x)) else Right((i - n, x)), {
              case Left((i, x)) => (i, x)
              case Right((i, x)) => (i + n, x)
            })
          )

  extension [X] (x: Power[X])
    private def split(n: Int): Material[? <: (Any, Any), List[X]] = 
      (n, x.power - n) match
        case (1, 1) =>
          Typed(x,Iso(x => (x.head, x.tail.head), (x, y) => List(x, y)))
        case (1, _) =>
          Typed(x, Iso(x => (x.head, x.tail), (x, y) => x::y))
        case (_, 1) =>
          Typed(x, Iso(x => (x.take(n), x.last), (x, y) => x :+ y))
        case (_, _) =>
          Typed(x, Iso(x => (x.take(n), x.drop(n)), (x, y) => x ::: y))

  private def sum[X, Y](x: Expr[X], y: Material[Y, ?]): Material[Either[X, Y], ?] = y match
    case Raw(y) => Raw(Sum(x, y))
    case Typed(expr, cons) => Typed(Sum(x, expr), Iso(_.map(cons.apply), _.map(cons.unapply)))

  private def product[X, Y](x: Expr[X], y: Material[Y, ?]): Material[(X, Y), ?] = y match
    case Raw(y) => Raw(Product(x, y))
    case Typed(expr, cons) =>  
      Typed(Product(x, expr), Iso((x, y) => (x, cons.apply(y)), (x, y) => (x, cons.unapply(y))))

  private def mu[T, R](v: Variable, mat: Material[T, R]): Material[T, R] = mat match
    case Raw(expr) => Raw(Mu(v, expr))
    case Typed(expr, cons) => Typed(Mu(v, expr), cons)

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
