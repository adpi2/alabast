package alabast

case class Variable(name: String, id: Int)

case class Context(depth: Int, variables: Map[String, Variable]):
  def next: (Variable, Context) =
    val variable = Variable(s"x$depth", variables.size)
    (variable, Context(depth + 1, variables + (variable.name -> variable)))

object Context:
  def apply(names: String*): Context = 
    val variables = names.zipWithIndex
      .map((name, index) => name -> Variable(name, index))
      .toMap
    Context(0, variables)

  given Context = Context("int", "long", "string")

  def in[T](f: Variable => Context ?=> T)(using ctx: Context): T = 
    val (x, next) = ctx.next
    f(x)(using next)

  val int: Material[Int, Int] = predef("int")
  val long: Material[Long, Long] = predef("long")
  val string: Material[String, String] = predef("string")
  
