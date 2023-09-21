// #Sireum #Logika
//@Logika: --manual --background type
import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._
import org.sireum.justification.natded.pred._

@pure def universal3[T](human: T => B @pure, mortal: T => B @pure, soul: T => B @pure): Unit = {
  Deduce(
    //@formatter:off
    (
      ∀{(x: T) => human(x) ->: mortal(x)},
      ∀{(y: T) => mortal(y) ->: soul(y)}
    ) ⊢ (
      ∀{(x: T) => human(x) ->: soul(x)}
    )
    Proof(
      1  (∀{(x: T) => human(x) ->: mortal(x)})   by Premise,
      2  (∀{(y: T) => mortal(y) ->: soul(y)})    by Premise,
      3  Let {(a: T) => SubProof(
        4  SubProof(
          5  Assume(human(a)),
          6  (human(a) ->: mortal(a))            by AllE[T](1),
          7  (mortal(a))                         by ImplyE(6, 5),
          8  (mortal(a) ->: soul(a))             by AllE[T](2),
          9  (soul(a))                           by ImplyE(8, 7)
        ),
       10  (human(a) ->: soul(a))                by ImplyI(4)
      )},
      11  (∀{(x: T) => human(x) ->: soul(x)})    by AllI[T](3)
    )
    //@formatter:on
  )
}