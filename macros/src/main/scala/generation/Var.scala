package generation

/**
 * Helper type allowing to pass functions as generic to macro.
 * Eg func. T,R (T -> R) -> R can be passed as (Var1 -> Var2) -> Var2
 */
sealed trait Var

sealed trait Var1 extends Var
sealed trait Var2 extends Var
sealed trait Var3 extends Var
sealed trait Var4 extends Var