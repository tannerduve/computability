import Computability.SingleOracle.TuringDegree
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Order.Hom.Basic

/-
Define the automorphism group of the Turing degrees.
-/
-- State and prove skeleton of countability argument

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

def computable_fns := { f : ℕ → ℕ // Computable f }

/-
Goal: Prove uncountably many Turing Degrees
Prove computable/partrec functions are countable
-/
-- #check Encodable.nonempty_encodable
-- #check exists_code_rel
-- Should use codeo
def partrecinj : computable_fns → ℕ :=
  sorry

#check @Encodable.ofLeftInjection ℕ computable_fns _root_.Nat.encodable

lemma NisCountable : Countable ℕ :=
  ⟨λ (n : ℕ) => Nat.succ n, Nat.succ_injective⟩

instance computable_functions_encodable : Encodable computable_fns :=
  -- ⟨λ _ => 0, λ _ => 0, λ _ => 0⟩
  sorry

lemma computable_functions_countable : Countable computable_fns := by
  unfold computable_fns
  sorry

theorem TuringDegree.automorphismGroup.isCountable : Countable (TuringDegree.automorphismGroup) := by
  sorry
