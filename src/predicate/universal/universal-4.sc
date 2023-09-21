// #Sireum #Logika

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._
import org.sireum.justification.natded.pred._

@pure def universal4[T](healthy: T => B @pure, happy: T => B @pure): Unit = {
  Deduce(
    //@formatter:off
    ∀{(x: T) => healthy(x) ->: happy(x)}  |-  (∀{(y: T) => healthy(y)} ->: ∀{(x: T) => happy(x)})
    Proof(
      1 #> ∀{(x: T) => healthy(x) ->: happy(x)}                   by Premise,
      2 #> SubProof(
        3 #> Assume(∀{(y: T) => healthy(y)}),
        4 #> Let { (a: T) => SubProof(
          5 #> healthy(a)                                         by AllE[T](3),
          6 #> (healthy(a) ->: happy(a))                          by AllE[T](1),
          7 #> happy(a)                                           by ImplyE(6, 5)
        )},
        8 #> ∀{(x: T) => happy(x)}                                by AllI[T](4)
      ),
      9 #> (∀{(y: T) => healthy(y)} ->: ∀{(x: T) => happy(x)})    by ImplyI(2)
    )
    //@formatter:on
  )
}
