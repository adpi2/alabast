package alabast

def permutations(n: Int): LazyList[Auto[Int]] = LazyList.from(perms(n - 1))

def variations(k: Int, n: Int): LazyList[Int => Int] = LazyList.from(vars(n - 1)(k - 1))

def combinations(k: Int, n: Int): LazyList[Seq[Int]] = combs(n - 1)(k - 1)

extension [A] (seq: Seq[A]):
  def tuples(n: Int): LazyList[List[A]] =
    Iterator.iterate(LazyList(List.empty[A])) { acc =>
      for 
        list <- acc
        a <- seq
      yield a :: list 
    }
    .drop(n).next // not really lazy

private val combs: LazyList[LazyList[LazyList[Seq[Int]]]] =
  LazyList.from(1).map { n =>
    LazyList.iterate(LazyList.from(0).map(Seq(_)).take(n)) { combs => 
      for 
        comb <- combs
        i <- (comb.last + 1) until n
      yield comb :+ i
    }
  }

private val vars: LazyList[LazyList[List[Int => Int]]] =
  LazyList.from(1).map { n =>
    LazyList.iterate(List.range(0, n).map(List(_))) { perms => 
      for
        perm <- perms
        i <- 0 until n
        if !perm.contains(i)
      yield i :: perm        
    }.map { perms =>
      perms.map(_.apply)
    }
  }

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
