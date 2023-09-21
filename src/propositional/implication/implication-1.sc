// #Sireum #Logika
//@Logika: --manual --background type

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._

@pure def implication1(p: B, q: B, r: B): Unit = {
  Deduce(
    //@formatter:off
    ((p & q) ->: r, p ->: q, p)  |-  r
    Proof(
      1 #> ((p & q) ->: r)       by Premise,
      2 #> (p ->: q)             by Premise,
      3 #> p                     by Premise,
      4 #> q                     by ImplyE(2, 3),
      5 #> (p & q)               by AndI(3, 4),
      6 #> r                     by ImplyE(1, 5),
    )
    //@formatter:on
  )
}
