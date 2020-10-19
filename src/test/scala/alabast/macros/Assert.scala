package alabast.macros

import scala.quoted._
import munit.FunSuite
import munit.Assertions._

inline def (inline suite: FunSuite) testAssert(inline name: String)(inline expr: Boolean): Unit =
  ${ testAssert(Some('name), 'suite, 'expr) }

inline def (inline suite: FunSuite) testAssert(inline expr: Boolean): Unit = 
  ${ testAssert(None, 'suite, 'expr) }

inline def (inline suite: FunSuite) testEquals(inline name: String)(inline left: Any, right: Any): Unit =
   $ { testEquals(Some('name), 'suite, 'left, 'right) }

inline def (inline suite: FunSuite) testEquals(inline left: Any, right: Any): Unit =
  $ { testEquals(None, 'suite, 'left, 'right) }

private def testAssert(name: Option[Expr[String]], suite: Expr[FunSuite], expr: Expr[Boolean])(using QuoteContext): Expr[Unit] =
  val spec = Expr(expr.unseal.pos.sourceCode)
  val testName = name.map(n => '{$n + ": " + $spec}).getOrElse(spec)
  '{ $suite.test($testName)(assert($expr)) }

private def testEquals(name: Option[Expr[String]], suite: Expr[FunSuite], left: Expr[Any], right: Expr[Any])(using QuoteContext): Expr[Unit] =
  val spec = Expr(left.unseal.pos.sourceCode + " should be " + right.unseal.pos.sourceCode)
  val testName = name.map(n => '{$n + ": " + $spec}).getOrElse(spec)
  '{ $suite.test($testName)(assertEquals($left, $right)) }
