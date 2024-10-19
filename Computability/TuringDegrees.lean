import Computability.TuringReductions
import Mathlib.Order.Lattice

-- Stuff about quotients is hidden in a namespace
namespace Hidden
universe u v

axiom Quot : {α : Sort u} → (α → α → Prop) → Sort u

axiom Quot.mk : {α : Sort u} → (r : α → α → Prop) → α → Quot r

axiom Quot.ind :
    ∀ {α : Sort u} {r : α → α → Prop} {β : Quot r → Prop},
      (∀ a, β (Quot.mk r a)) → (q : Quot r) → β q

axiom Quot.lift :
    {α : Sort u} → {r : α → α → Prop} → {β : Sort u} → (f : α → β)
    → (∀ a b, r a b → f a = f b) → Quot r → β

axiom Quot.sound :
      ∀ {α : Type u} {r : α → α → Prop} {a b : α},
        r a b → Quot.mk r a = Quot.mk r b
end Hidden

-- We can now define a setoid on functions from ℕ to ℕ under the turing equivalence relation
instance : Setoid (ℕ →. ℕ) where
  r := turing_equivalent
  iseqv := ⟨turing_equiv_refl, @turing_equiv_symmetric, @turing_equiv_trans⟩

-- Define the Turing degrees as the set of equivalence classes under turing equivalence
def TuringDegrees := Quot turing_equivalent

-- Define the join operation on partial functions:
def join (f g : ℕ →. ℕ) : ℕ →. ℕ :=
  λ n => if n % 2 = 0 then f (n / 2) else g (n / 2)

infix:99 "⊕" => join

/-
To do - We want to show Turing degrees form an upper semilattice.

To do this we need to lift our join operation and the turing reducibility
relation to Turing degrees. This requires an explicit proof that 
the operations and relations respect the equivalence, ie:

∀ f g f' g', f ≡ᵀ f' → g ≡ᵀ g' → f ⊕ g ≡ᵀ f' ⊕ g'
∀ f g f' g', f ≡ᵀ f' → g ≡ᵀ g' → f ≤ᵀ g → f' ≤ᵀ g'

Once we've done this, we prove that the lifted operations and relations
form a semilattice, ie. a lattice with a bottom element and a join operation.
-/

-- Lift the join operation to Turing degrees via quotient construction
def TuringDegrees.join (d₁ d₂ : TuringDegrees) : TuringDegrees :=
  sorry

-- Lift the turing reducibility relation to Turing degrees via quotient construction
def TuringDegrees.turing_reducible (d₁ d₂ : TuringDegrees) : Prop :=
  sorry

-- Prove that Turing Degrees forms an upper semilattice
instance : SemilatticeSup TuringDegrees where
  sup := TuringDegrees.join
  le := TuringDegrees.turing_reducible
  le_refl := sorry
  le_trans := sorry
  le_antisymm := sorry
  le_sup_left := sorry
  le_sup_right := sorry
  sup_le := sorry
