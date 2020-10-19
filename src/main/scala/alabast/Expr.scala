package alabast

import Comparison._

sealed trait Expr[T]:
  type R = T

case object Zero extends Expr[Nothing]
case object One extends Expr[Unit]
final case class Predef[T](variable: Variable) extends Expr[T]
final case class Product[A, B](fst: Expr[A], snd: Expr[B]) extends Expr[(A, B)]
final case class Sum[A, B](left: Expr[A], right: Expr[B]) extends Expr[Either[A, B]]
final case class Mu[F](mu: Variable, unmu: Expr[F]) extends Expr[F]

object Expr:
  private def sum[X, Y](x: Expr[X], y: Material[Y, ?]): Material[Either[X, Y], ?] = y match
    case Raw(y) => Raw(Sum(x, y))
    case Typed(expr, apply, unapply) => Typed(Sum(x, expr), _.map(apply), _.map(unapply))

  private def product[X, Y](x: Expr[X], y: Material[Y, ?]): Material[(X, Y), ?] = y match
    case Raw(y) => Raw(Product(x, y))
    case Typed(expr, apply, unapply) =>  
      Typed(Product(x, expr), (x, y) => (x, apply(y)), (x, y) => (x, unapply(y)))
  
  extension [X, Y] (x: Expr[X])
    def show: String = x match
      case Zero => "zero" // 0
      case One => "one"
      case Predef(v) => v.name
      case Sum(left, right) => s"${left.show} + ${right.show}"
      case Product(fst, snd) => s"${fst.show} * ${snd.show}"
      case Mu(mu, unmu) => s"mu(${mu.name} => ${unmu.show})"

    def + (y: Expr[Y]): Material[Either[X, Y], ?] = (x, y) match
      case (Zero, y) => Raw(y).imap(Right[X, Y])(_ => absurd) // 00
      case (x, Zero) => Raw(x).imap(Left[X, Y])(_ => absurd) // 10
      case (Sum(left, right), y) =>
        if y >= left then Typed(Sum(y, x), _.swap, _.swap) // 20
        else // 21
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
      case (x, Sum(left, right)) =>
        if x >= left then Raw(Sum(x, y)) // 30
        else // 31
          sum(left, (x + right)).imap {
            case Left(y) => Right(Left(y))
            case Right(Left(x)) => Left(x) 
            case Right(Right(z)) => Right(Right(z))
          } {
            case Left(x) => Right(Left(x))
            case Right(Left(y)) => Left(y)
            case Right(Right(z)) => Right(Right(z))
            case Right(_) => absurd // should not be needed
          }
      case (x, y) => 
        if(x >= y) Raw(Sum(x, y))
        else Typed(Sum(y, x), _.swap, _.swap) // 40

    def * (y: Expr[Y]): Material[(X, Y), ?] = (x, y) match
      case (Zero, _) => zero // 00
      case (_, Zero) => zero // 10
      case (One, y) => Typed(y, ((), _), _(1)) // 20
      case (x, One) => Typed(x, (_, ()), _(0)) // 30
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
      case (Product(xFst, xSnd), Product(yFst, ySnd)) =>
        if xFst > yFst // 60
          product(xFst, xSnd * y).imap
            { case (x1, (x2, y)) => ((x1, x2), y) }
            { case ((x1, x2), y) => (x1, (x2, y)) }
        else // 61
          product(yFst, x * ySnd).imap 
            { case (y1, (x, y2)) => (x, (y1, y2)) }
            { case (x, (y1, y2)) => (y1, (x, y2)) }
      case (Product(fst, snd), y) =>
        if  fst > y // 70
          product(fst, snd * y).imap
            { case (x1, (x2, y)) => ((x1, x2), y) }
            { case ((x1, x2), y) => (x1, (x2, y)) }
        else Typed(Product(y, x),_.swap, _.swap) // 71
      case (x, Product(fst, snd)) =>
        if x > fst then Raw(Product(x, y)) // 80
        else //81
          product(fst, x * snd).imap
            { case (y1, (x, y2)) => (x, (y1, y2)) }
            { case (x, (y1, y2)) => (y1, (x, y2)) }
      case (x, y) => 
        if x >= y then Raw(Product(x, y))
        else Typed(Product(y, x),_.swap, _.swap) // 90
      
    
    def subtract(term: Expr[Y]): Option[Expr[?]] = (x, term) match
      case (x, Zero) => Some(x) // 00
      case (Sum(left, right), Sum(termLeft, termRight)) =>
        order.compare(left, termLeft) match
          case Equal => right.subtract(termRight) // 10
          case Greater => 
            right.subtract(term).map { 
              case Zero => left // 11
              case diff => Sum(left, diff) // 12
            }
          case Lower => None // 13
      case (Sum(left, right), term) =>
        order.compare(left, term) match
          case Equal => Some(right) // 20
          case Greater => 
            right.subtract(term).map { 
              case Zero => left // 21
              case diff => Sum(left, diff) //22
            }
          case Lower => None // 23
      case (x, term) =>
        order.compare(x, term) match
          case Equal => Some(Zero) // 30
          case _ => None // 31

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

      // def [X, Y] (x: Expr[X])
    def asProduct(div: Expr[Y]): Option[AsProduct[Y, ?, X]] =
      (x, div) match
        case (Zero, _) => Some(AsProduct(zero, Zero)) // 00
        case (_, One) => Some( // 10
          AsProduct(Typed(x, (x => ((), x)), ((_, x) => x)), x)
        )
        
        case (Sum(left, right), Sum(divLeft, divRight)) =>
          left.asProduct(divLeft).flatMap { leftLeftAsProduct => // 20
            val leftRight: Material[(divRight.R, leftLeftAsProduct.Snd), ?] = Raw(divRight) * Raw(leftLeftAsProduct.snd)
            for
              remainder <- right.subtract(leftRight.expr) // 21
              rightAsProduct <- remainder.asProduct(div) // 22
            yield // 23 // 24
              val leftUnderlying: Material[(Y, leftLeftAsProduct.Snd), ?] = 
                (leftLeftAsProduct.underlying + leftRight)
                  .imap {
                    case Left((y, x)) => (Left(y), x)
                    case Right((y, x)) => (Right(y), x)
                  } { (y, x) => y.map((_, x)).left.map((_, x)) }
              val leftAsProduct =
                AsProduct(
                  leftUnderlying.withRaw[left.R],
                  leftLeftAsProduct.snd
                )
              
              sumAsProduct(leftAsProduct, rightAsProduct)
          }

        
        case (Sum(left, right), div) =>
          for
            leftProduct <- left.asProduct(div) // 30
            rightProduct <- right.asProduct(div) // 31
          yield // 32
            val underlying : Material[(Y, Either[leftProduct.Snd, rightProduct.Snd]), ?] =
                (leftProduct.underlying + rightProduct.underlying).imap {
                  case Left((y, x)) => (y, Left(x))
                  case Right((y, x)) => (y, Right(x))
                } { (y, x) =>  x.map((y, _)).left.map((y, _)) }
            // cannot prove that (left + right).R =:= X
            AsProduct(underlying.withRaw[X], Sum(leftProduct.snd, rightProduct.snd))
            
        case (_, Sum(_, _)) => None // 40

        case (Product(fst, snd), Product(fstDiv, sndDiv)) =>
          order.compare(fst, fstDiv) match
            case Equal => 
              for sndProduct <- snd.asProduct(sndDiv) // 50
              yield // 51
                val underlying = 
                  product(fstDiv, sndProduct.underlying).imap 
                    { case (fst, (snd, x)) => ((fst, snd), x) }
                    { case ((fst, snd), x) => (fst, (snd, x)) }
                // cannot prove that (fst * snd).R =:= X
                AsProduct(underlying.withRaw[X], sndProduct.snd)
            case Greater => 
              for sndProduct <- snd.asProduct(div) // 52
              yield productAsProduct(fst, sndProduct)
            case Lower => None // 54

        case (Product(`div`, snd), _) =>
          Some(AsProduct(Raw(Product(div, snd)), snd)) // 60
        case (Product(fst, snd), _) =>
          for sndProduct <- snd.asProduct(div) // 61
          yield productAsProduct(fst, sndProduct)
        case (_, Product(_, _)) => None // 70
        case (`div`, _) =>
          val underlying = Raw(x).imap { (_, ()) } { _(0) } 
          Some(AsProduct(underlying, One))
        case _ => None

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
