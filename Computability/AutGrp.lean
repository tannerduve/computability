import Computability.TuringDegree
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Order.Hom.Basic

/--
Turing degrees are the equivalence classes of partial functions under Turing equivalence.
-/

instance TuringDegree.isPartialOrder : PartialOrder TuringDegree :=
  @instPartialOrderAntisymmetrization (ℕ →. ℕ)
    {le := TuringReducible, le_refl := TuringReducible.refl, le_trans := @TuringReducible.trans}
/-
Define the automorphism group of the Turing degrees.
-/

-- Define join of Turing Degrees
-- Define an automorphism as a bijection `f : TuringDegrees → TuringDegrees`
-- preserving and reflecting order
-- State and prove skeleton of countability argument

/-
Add to Mathlib. Maybe generalize over any relation.
-/
abbrev OrderAut (α : Type*) [LE α] := OrderIso α α

instance OrderAutGroup (α : Type) [LE α] : Group (OrderAut α) where
  mul := OrderIso.trans
  one := OrderIso.refl α
  inv := OrderIso.symm
  mul_assoc := fun a b c => OrderIso.ext rfl
  one_mul := fun a => OrderIso.ext rfl
  mul_one := fun a => OrderIso.ext rfl
  inv_mul_cancel := OrderIso.symm_trans_self

def TuringDegree.automorphismGroup : Type := OrderAut TuringDegree

instance TuringDegree.automorphismGroup.isGroup : Group (TuringDegree.automorphismGroup) :=
  OrderAutGroup TuringDegree

theorem TuringDegree.automorphismGroup.isCountable : Countable (TuringDegree.automorphismGroup) :=
  sorry
