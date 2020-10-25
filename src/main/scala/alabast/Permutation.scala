package alabast

def permutations(n: Int): Seq[Auto[Int]] = 
  if n == 1 then Seq(Auto(_ => 0,  _ => 0))
  else for
    f <- permutations(n - 1)
    k <- 0 until n
  yield Auto(
    i => 
      if i < k then f.apply(i)
      else if i == k then n - 1
      else f.apply(i - 1),
    i =>
      if i == n - 1 then k
      else
        val r = f.unapply(i)
        if r < k then r
        else r + 1
  )
