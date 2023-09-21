// #Sireum #Logika
//@Logika: --manual --background type

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._

@pure def implication4b(p: B, q: B): Unit = {
  Deduce(
    //@formatter:off
    |-  (p ->: (q ->: p))
    Proof(
      1 #> SubProof(
        2 #> Assume(p),
        3 #> SubProof(
          4 #> Assume(q),
          5 #> p               by Premise
        ),
        6 #> (q ->: p)         by ImplyI(3)
      ),
      7 #> (p ->: (q ->: p))   by ImplyI(1),
    )
    //@formatter:on
  )
}