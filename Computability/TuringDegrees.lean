import Computability.TuringReductions
import Mathlib.GroupTheory.Perm.Basic

/--
Turing degrees are the equivalence classes of partial functions under Turing equivalence.
-/
abbrev TuringDegree :=
  Antisymmetrization _ TuringReducible

instance TuringDegree.isPartialOrder : PartialOrder TuringDegree :=
  @instPartialOrderAntisymmetrization (ℕ →. ℕ)
    {le := TuringReducible, le_refl := TuringReducible.refl, le_trans := @TuringReducible.trans}

/-
Define the automorphism group of the Turing degrees.
-/

-- Define join of Turing Degrees
-- Define an automorphism as a bijection `f : TuringDegrees → TuringDegrees`
-- preserving and reflecting order and join
-- State and prove skeleton of countability argument
