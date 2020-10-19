package alabast

import Comparison._

enum Comparison:
  case Greater
  case Lower
  case Equal

extension (x: Comparison)
  def orElse(y: => Comparison): Comparison = x match
    case Equal => y
    case _ => x

trait Order[A]:
  def compare(x: A, y: A): Comparison
  extension (x: A)
    def >(y: A): Boolean = compare(x, y) == Greater
    def >=(y: A): Boolean = compare(x, y) != Lower
    def <(y: A): Boolean = compare(x, y) == Lower
    def <=(y: A): Boolean = compare(x, y) != Greater

def order[A](using o: Order[A]): Order[A] = o

given Order[Int]:
  def compare(x: Int, y: Int): Comparison = x - y match
    case c if c > 0 => Greater
    case 0 => Equal
    case _ => Lower

given Order[Expr[?]]:
  def compare(x: Expr[?], y: Expr[?]): Comparison = (x, y) match
    case (Sum(xLeft, xRight), Sum(yLeft, yRight)) => 
      compare(xLeft, yLeft).orElse(compare(xRight, yRight))
    case (Sum(xLeft, _), y) => compare(xLeft, y).orElse(Greater)
    case (x, Sum(yLeft, _)) => compare(x, yLeft).orElse(Lower)
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
