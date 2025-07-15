import Computability.SingleOracle.TuringDegree
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Order.Hom.Basic

/-
Define the automorphism group of the Turing degrees.
-/
-- State and prove skeleton of countability argument

/-
Add order automorphism + group instance to Mathlib. Maybe generalize over any relation (RelIso). (Doesnt seem to be in mathlib but not sure)
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

instance TuringDegree.automorphismGroup.existsAut : Inhabited (TuringDegree.automorphismGroup) :=
  ⟨OrderIso.refl TuringDegree⟩

theorem TuringDegree.automorphismGroup.isCountable : Countable (TuringDegree.automorphismGroup) :=
  sorry
