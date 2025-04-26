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

-- Notation for orderings lifted to degrees
infix:99 " ≤ᵀ⋆ " => TuringDegree.isPartialOrder.le
/-
Define the automorphism group of the Turing degrees.
-/

-- Define join of Turing Degrees
-- Define an automorphism as a bijection `f : TuringDegrees → TuringDegrees`
-- preserving and reflecting order
-- State and prove skeleton of countability argument

/-
Join of two partial functions
-/
def gjoin {α β α' β' : Type} [Primcodable α] [Primcodable β] [Primcodable α'] [Primcodable β']
(f : α →. β) (g : α' →. β') : α ⊕ α' →. β ⊕ β' :=
  λ x =>
    match x with
    | Sum.inl a => (f a).map (λ b => Sum.inl b)
    | Sum.inr b => (g b).map (λ a' => Sum.inr a')

infix :50 " ⊕ " => gjoin

def order_aut {α : Type} [PartialOrder α] (f : α → α) : Prop :=
  ∀ a b : α, a ≤ b ↔ f a ≤ f b

def PartialOrder.automorphismGroup (α : Type) [PartialOrder α] : Type :=
  { f : Equiv.Perm α // order_aut f }

instance OrderAutGroup (α : Type) [PartialOrder α] : Group (PartialOrder.automorphismGroup α) where
  mul := fun f g => ⟨f.1 * g.1, by {
    intro a b
    constructor
    intro aleb
    simp
    have t1 : ∀ a b : α, a ≤ b ↔ f.1 a ≤ f.1 b := f.2
    have t2 : ∀ a b : α, a ≤ b ↔ g.1 a ≤ g.1 b := g.2
    specialize t1 (g.1 a) (g.1 b)
    apply t1.1
    specialize t2 a b
    apply t2.1
    exact aleb
    intro fgleb
    simp at fgleb
    have t1 : ∀ a b : α, a ≤ b ↔ f.1 a ≤ f.1 b := f.2
    have t2 : ∀ a b : α, a ≤ b ↔ g.1 a ≤ g.1 b := g.2
    specialize t1 (g.1 a) (g.1 b)
    specialize t2 a b
    apply t2.2
    apply t1.2
    exact fgleb
  }⟩
  one := ⟨1, by {
    intro a b
    constructor
    intro aleb
    simp
    apply aleb
    intro fgleb
    simp at fgleb
    apply fgleb
  }⟩
  inv := fun f => ⟨(f.1)⁻¹, by {
    intro a b
    constructor
    intro aleb
    have t1 : ∀ a b : α, a ≤ b ↔ f.1 a ≤ f.1 b := f.2
    specialize t1 (f.1⁻¹ a) (f.1⁻¹ b)
    apply t1.2
    simp
    apply aleb
    intro fgleb
    have t1 : ∀ a b : α, a ≤ b ↔ f.1 a ≤ f.1 b := f.2
    specialize t1 (f.1⁻¹ a) (f.1⁻¹ b)
    simp at *
    apply t1.1
    apply fgleb
  }⟩
  mul_assoc := by {
    intro f g h
    constructor
  }
  one_mul := by {
    intro f
    constructor
  }
  mul_one := by {
    intro f
    constructor
  }
  inv_mul_cancel := by {
    intro f
    apply Subtype.ext
    simp [Equiv.Perm.mul_def, Equiv.Perm.inv_def]
    -- weird case here? simp and constructor not doing anything
    sorry
  }

def TuringDegree.automorphismGroup : Type := PartialOrder.automorphismGroup TuringDegree

instance TuringDegree.automorphismGroup.isGroup : Group (TuringDegree.automorphismGroup) :=
  OrderAutGroup TuringDegree
