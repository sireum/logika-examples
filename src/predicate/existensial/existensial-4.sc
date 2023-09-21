// #Sireum #Logika
//@Logika: --manual --background type
import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._
import org.sireum.justification.natded.pred._

@pure def existential4[T](human: T => B @pure, mortal: T => B @pure): Unit = {
  Deduce(
    //@formatter:off
    (
      ∀{(x: T) => human(x) ->: mortal(x)},
      ∃{(y: T) => human(y)}
    ) ⊢ (
      ∃{(z: T) => mortal(z)}
    )
    Proof(
      1  (∀{(x: T) => human(x) ->: mortal(x)})   by Premise,
      2  (∃{(y: T) => human(y)})                 by Premise,
      3  Let {(a: T) => SubProof(
        4  Assume(human(a)),
        5  (human(a) ->: mortal(a))              by AllE[T](1),
        6  (mortal(a))                           by ImplyE(5, 4),
        7  (∃{(z: T) => mortal(z)})              by ExistsI[T](6)
      )},
      8 #> ∃{(z: T) => mortal(z)}                by ExistsE[T](2, 3),
    )
    //@formatter:on
  )
}

@pure def existential5(vowel: C => B @pure, covered: Z => B @pure, holds: (Z, C) => B @pure, gameOver: B): Unit = {
  Deduce(
    //@formatter:off
    (
      ∃{(s: Z) => covered(s) & ∃{(c: C) => vowel(c) & holds(s, c)}},
      ∃{(x: Z) => covered(x)} ->: !gameOver
    ) |- (
      !gameOver
      )
      Proof(
      1 #> ∃{(s: Z) => covered(s) & ∃{(c: C) => vowel(c) & holds(s, c)}}   by Premise,
      2 #> (∃{(x: Z) => covered(x)} ->: !gameOver)                         by Premise,
      3 #> Let { (a: Z) => SubProof(
        4 #> Assume(covered(a) & ∃{(c: C) => vowel(c) & holds(a, c)}),
        5 #> covered(a)                                                    by AndE1(4),
        6 #> ∃{(x: Z) => covered(x)}                                       by ExistsI[Z](5)
      )},
      7 #> ∃{(x: Z) => covered(x)}                                         by ExistsE[Z](1, 3),
      8 #> (!gameOver)                                                     by ImplyE(2, 7),
    )
    //@formatter:on
  )
}
