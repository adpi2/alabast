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
