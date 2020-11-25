package alabast.macros

import munit.FunSuite
import scala.quoted._
import munit.Assertions._

class TestSuite extends FunSuite:
  inline def testAssert(inline expr: Boolean): Unit = 
    ${ testAssertImpl('None, 'this, 'expr) }
  
  inline def testAssert(inline name: String)(inline expr: Boolean): Unit =
    ${ testAssertImpl('{Option(name)}, 'this, 'expr) }
  
  inline def testEquals(inline left: Any, inline right: Any): Unit =
    $ { testEqualsImpl('None, 'this, 'left, 'right) }
  
  inline def testEquals(inline name: String)(inline left: Any, right: Any): Unit =
    $ { testEqualsImpl('{Option(name)}, 'this, 'left, 'right) }

def testAssertImpl(name: Expr[Option[String]], suite: Expr[FunSuite], expr: Expr[Boolean])(using QuoteContext): Expr[Unit] =
  val spec = Expr(expr.unseal.pos.sourceCode)
  val testName = '{$name.map(n => n + ": " + $spec).getOrElse($spec)}
  '{ $suite.test($testName)(assert($expr)) }

def testEqualsImpl(name: Expr[Option[String]], suite: Expr[FunSuite], left: Expr[Any], right: Expr[Any])(using QuoteContext): Expr[Unit] =
  val spec = Expr(left.unseal.pos.sourceCode + " should be " + right.unseal.pos.sourceCode)
  val testName = '{$name.map(n => n + ": " + $spec).getOrElse($spec)}
  '{ $suite.test($testName)(assertEquals($left, $right)) }
