package alabast

private val perms: LazyList[Array[Auto[Int]]] =
  LazyList.iterate((1, Array(Auto[Int](_ => 0, _ => 0)))) { (n, autos) =>
    val result = for
      auto <- autos
      k <- 0 until (n + 1)
    yield Auto[Int](
      i => 
        if i < k then auto.apply(i)
        else if i == k then n
        else auto.apply(i - 1),
      i =>
        if i == n then k
        else
          val r = auto.unapply(i)
          if r < k then r
          else r + 1
    )
    (n + 1, result)
  }.map(_(1))

def permutations(n: Int): LazyList[Auto[Int]] = LazyList.from(perms(n - 1))

extension [A] (seq: Seq[A]):
  def tuples(n: Int): LazyList[List[A]] =
    Iterator.iterate(LazyList(List.empty[A])) { acc =>
      for 
        list <- acc
        a <- seq
      yield a :: list 
    }
    .drop(n).next // not really lazy