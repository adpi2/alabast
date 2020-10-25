package alabast

trait Functor[F[_]]:
  extension [A, B] (fa: F[A]) def map(f: A => B): F[B]
