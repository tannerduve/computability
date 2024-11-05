import Computability.Encoding
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
instance TD : Setoid (ℕ →. ℕ) where
  r := turing_equivalent
  iseqv := ⟨turing_equiv_refl, @turing_equiv_symmetric, @turing_equiv_trans⟩

-- Define the Turing degrees as the set of equivalence classes under turing equivalence
def TuringDegree := Quot turing_equivalent

-- Define the join operation on partial functions:
def join (f g : ℕ →. ℕ) : ℕ →. ℕ :=
  λ n =>
    if n % 2 = 0 then
      (f (n / 2)).map (λ x => 2 * x)
    else
      (g (n / 2)).map (λ y => 2 * y + 1)

infix:99 "⊔" => join

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

#check Quot.lift

theorem reduce_lifts : ∀ (a b : ℕ →. ℕ), a ≡ᵀ b → (f ≤ᵀ a ↔ f ≤ᵀ b) := by
  intros a b aEqb
  constructor
  intro fReda
  unfold turing_equivalent at *
  cases' aEqb with lt rt
  apply turing_reduce_trans fReda lt
  intro fRedb
  unfold turing_equivalent at *
  cases' aEqb with lt rt
  apply turing_reduce_trans fRedb rt

theorem reduce_lifts₁ : ∀ (a b₁ b₂ : ℕ →. ℕ), b₁≡ᵀb₂ → (a≤ᵀb₁) = (a≤ᵀb₂) := by
  intros a b₁ b₂ bEqb
  apply propext
  constructor
  intro aRedb₁
  unfold turing_equivalent at *
  apply turing_reduce_trans aRedb₁ bEqb.1
  intro aRedb₂
  unfold turing_equivalent at *
  apply turing_reduce_trans aRedb₂ bEqb.2

theorem reduce_lifts₂ : ∀ (f g h : ℕ →. ℕ), f ≡ᵀ g → (turing_reducible f h = turing_reducible g h) := by
  intros f g h fEqg
  apply propext
  constructor
  intro fRedh
  unfold turing_equivalent at *
  apply turing_reduce_trans fEqg.2 fRedh
  intro gRedh
  unfold turing_equivalent at *
  apply turing_reduce_trans fEqg.1 gRedh

-- Lift the turing reducibility relation to Turing degrees via quotient construction
def TuringDegree.turing_red (d₁ d₂ : TuringDegree) : Prop :=
  @Quot.lift₂ _ _ Prop (turing_equivalent) (turing_equivalent) (turing_reducible) (reduce_lifts₁) (reduce_lifts₂) d₁ d₂

theorem join_lifts₁ : ∀ (a b₁ b₂ : (ℕ →. ℕ)), turing_equivalent b₁ b₂ → (Quot.mk turing_equivalent (join a b₁)) = (Quot.mk turing_equivalent (join a b₂)) := by
  sorry

theorem join_lifts₂ : ∀ (a₁ a₂ b : (ℕ →. ℕ)), turing_equivalent a₁ a₂ → (Quot.mk turing_equivalent (join a₁ b)) = (Quot.mk turing_equivalent (join a₂ b)) := by
  sorry

-- Lift the join operation to Turing degrees via quotient construction
def TuringDegree.join (d₁ d₂ : TuringDegree) : TuringDegree := by
  apply Quot.lift₂ _ _ _ d₁ d₂
  intros f g
  apply Quot.mk turing_equivalent (f ⊔ g)
  intros f g h gEqh
  apply join_lifts₁ f g h gEqh
  intros f g h fEqg
  apply join_lifts₂ f g h fEqg

def jump (f : ℕ →. ℕ) : ℕ →. ℕ :=
λ e => (φ f e) e

#check Quot.lift

theorem jump_lifts : ∀ (a b : ℕ →. ℕ), a ≡ᵀ b → (Quot.mk turing_equivalent (jump a)) = (Quot.mk turing_equivalent (jump b)) := by
  sorry

-- Lift the jump operator to Turing degrees via quotient construction
def TuringDegree.jump (d : TuringDegree) : TuringDegree :=
  @Quot.lift _ _ _ _ (jump_lifts) d

-- Prove that Turing Degrees forms an upper semilattice
instance : SemilatticeSup TuringDegree where
  sup := TuringDegree.join
  le := TuringDegree.turing_red
  le_refl := by
    apply Quot.ind
    intro a
    apply turing_reduce_refl
  le_trans := by
    apply Quot.ind
    intros a b c aRedb bRedc
    sorry
  le_antisymm := by sorry
  le_sup_left := sorry
  le_sup_right := sorry
  sup_le := sorry
