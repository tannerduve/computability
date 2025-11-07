import Computability.Oracle
import Computability.Jump
import Computability.TuringDegree

namespace TDWishlist
noncomputable section
open Computability

/-- A fixed computable partial function; its degree is the bottom degree `0`. -/
def zero_pf : ℕ →. ℕ := fun _ => Part.some 0
-- /-- Notation for the (intended) least Turing degree `0`. -/
def turing_degree_mk : (ℕ →. ℕ) → TuringDegree := fun f => ⟦f⟧

def deg0 : TuringDegree := ⟦zero_pf⟧

def halt_pf : ℕ →. ℕ := jump zero_pf

def halting_degree : TuringDegree := ⟦halt_pf⟧

-- def ce_pf (f : ℕ →. ℕ) : Prop := ∃ A : Set ℕ, turing_degree_mk f = turing_degree_mk ↑(fun a => if a ∈ A then Part.some 1 else Part.some 0)
-- just cast

-- def ce_degree (d : TuringDegree) : Prop := ∃ f, ce_pf f ∧ ⟦f⟧ = d


-- jump
def low (d : TuringDegree) : Prop := d = halting_degree

lemma join_degree_lifts : ∀ (a₁ b₁ a₂ b₂ : ℕ →. ℕ),
                          a₁ ≡ᵀ a₂ → b₁ ≡ᵀ b₂ →
                          turing_degree_mk (a₁ ⊕ b₁) = turing_degree_mk (a₂ ⊕ b₂) := by
  intro f₁ f₂ g₁ g₂ hf hg
  apply Quot.sound
  simp [AntisymmRel]
  constructor
  cases' hf with hf₁ hf₂
  cases' hg with hg₁ hg₂
  case a.left =>
    have f₁g₁g₂ : f₁ ≤ᵀ (g₁ ⊕ g₂) := TuringReducible.trans hf₁ (left_le_join g₁ g₂)
    have f₂g₁g₂ : f₂ ≤ᵀ (g₁ ⊕ g₂) := TuringReducible.trans hg₁ (right_le_join g₁ g₂)
    apply join_le f₁ f₂ (g₁ ⊕ g₂) f₁g₁g₂ f₂g₁g₂
  case a.right =>
    cases' hf with hf₁ hf₂
    cases' hg with hg₁ hg₂
    have gf₁f₂ : g₁ ≤ᵀ (f₁ ⊕ f₂) := TuringReducible.trans hf₂ (left_le_join f₁ f₂)
    have g₂f₁f₂ : g₂ ≤ᵀ (f₁ ⊕ f₂) := TuringReducible.trans hg₂ (right_le_join f₁ f₂)
    apply join_le g₁ g₂ (f₁ ⊕ f₂) gf₁f₂ g₂f₁f₂

def TuringDegree.join (a b : TuringDegree) : TuringDegree :=
  Quotient.liftOn₂ a b (fun f g => ⟦f ⊕ g⟧) join_degree_lifts

lemma TuringDegree.left_le_join {a b : TuringDegree} : a ≤ (a ⊕ b) := sorry

lemma TuringDegree.right_le_join {a b : TuringDegree} : b ≤ (a ⊕ b) := sorry

def deg0_le (d : TuringDegree) : deg0 ≤ d := by sorry

theorem join_add_function_add : ∀ (a b : TuringDegree) (A B : ℕ →. ℕ), ⟦A⟧ = a → ⟦B⟧ = b → ⟦A ⊕ B⟧ = (a ⊕ b) := sorry

lemma computable_deg0 (f : ℕ → ℕ) (hf : Computable f) : deg0 = turing_degree_mk f := sorry

-- lemma posts_problem : ∃ c : TuringDegree, ce_degree c ∧ deg0 < c ∧ c < halting_degree := sorry

lemma exists_incomparable : ∃ a b : TuringDegree, ¬ a ≤ b ∧ ¬ b ≤ a := sorry

lemma sacks_density_below_jump {a b : TuringDegree} : a < b → b ≤ halting_degree → ∃ c, a < c ∧ c < b := sorry

lemma no_top_degree : ∀ t : TuringDegree, ∃ d, t ≤ d := by sorry

-- /-! 5. Degree-level join gives an upper semilattice. -/
-- infix:50 " ⩔ " => (fun a b : TuringDegree => -- degree join you defined via `Quot.liftOn₂`
--   (by exact (TuringDegree.add a b)))  -- alias to reference in this wishlist
-- /-- English: `a ⩔ b = b ⩔ a`. -/
-- axiom sup_comm   (a b : TuringDegree) : a ⩔ b = b ⩔ a
-- /-- English: `(a ⩔ b) ⩔ c = a ⩔ (b ⩔ c)`. -/
-- axiom sup_assoc  (a b c : TuringDegree) : (a ⩔ b) ⩔ c = a ⩔ (b ⩔ c)
-- /-- English: `a ⩔ a = a`. -/
-- axiom sup_idem   (a : TuringDegree) : a ⩔ a = a
-- /-- English: `a ≤ a ⩔ b`. -/
-- axiom le_sup_left  (a b : TuringDegree) : a ≤ a ⩔ b
-- /-- English: `b ≤ a ⩔ b`. -/
-- axiom le_sup_right (a b : TuringDegree) : b ≤ a ⩔ b
-- /-- English: LUB law on degrees: if `a ≤ c` and `b ≤ c` then `a ⩔ b ≤ c`. -/
-- axiom sup_le (a b c : TuringDegree) : a ≤ c → b ≤ c → a ⩔ b ≤ c


-- /-! 10. Density inside the c.e. degrees (Lachlan–Sacks). -/
-- /-- English: If `a < b` are c.e. degrees, there is a c.e. `c` with `a < c < b`. -/
-- axiom ce_density {a b : TuringDegree} :
--   CE a → CE b → a < b → ∃ c, CE c ∧ a < c ∧ c < b

-- /-! 11. Splitting theorem (c.e.). -/
-- /-- English: Every nonzero c.e. degree splits into two incomparable smaller c.e. degrees with join equal to it. -/
-- axiom ce_splitting (a : TuringDegree) :
--   CE a → a ≠ deg0 →
--   ∃ b c, CE b ∧ CE c ∧ b < a ∧ c < a ∧ (¬ b ≤ c) ∧ (¬ c ≤ b) ∧ (b ⩔ c = a)

-- /*- 12. Minimal pair (c.e.). -*/
-- /-- English: There exist incomparable c.e. degrees `b,c` with `b ⩔ c = 0'` (a minimal pair for `0'`). -/
-- axiom ce_minimal_pair_below_jump :
--   ∃ b c, CE b ∧ CE c ∧ (¬ b ≤ c) ∧ (¬ c ≤ b) ∧ (b ⩔ c = degreeJump deg0)

-- /-! 13. Existence of a (non-c.e.) minimal degree. -/
-- /-- English: There exists `m > 0` with no degree strictly between `0` and `m`. -/
-- axiom minimal_degree_exists :
--   ∃ m, deg0 < m ∧ ¬ ∃ d, deg0 < d ∧ d < m ∧ True

-- /-! 14. No greatest degree. -/
-- /-- English: There is no top degree (e.g. because `a < a'` always). -/
-- axiom no_top_degree : ¬ ∃ t : TuringDegree, ∀ d, d ≤ t

-- /-! 15. Jump inversion (global). -/
-- /-- English: For every `b ≥ 0'` there exists `a` with `a' = b`. -/
-- axiom jump_inversion {b : TuringDegree} :
--   degreeJump deg0 ≤ b → ∃ a, degreeJump a = b

-- /-! 16. Jump inversion (c.e. case). -/
-- /-- English: If `b` is c.e. and `b ≥ 0'`, there is a c.e. `a` with `a' = b`. -/
-- axiom ce_jump_inversion {b : TuringDegree} :
--   CE b → degreeJump deg0 ≤ b → ∃ a, CE a ∧ degreeJump a = b

-- /-! 17. Low Basis Theorem (degree form). -/
-- /-- English: There exist nonzero low c.e. degrees; more generally, every nonempty Π⁰₁ class has a path of low degree. -/
-- axiom exists_low_ce_nonzero : ∃ a, CE a ∧ Low a ∧ deg0 < a

-- /-! 18. Cone avoidance (Π⁰₁ basis, degree form). -/
-- /-- English: For any degree `d`, there is a noncomputable set of degree not above `d` in some Π⁰₁ class. -/
-- axiom cone_avoidance_exists (d : TuringDegree) :
--   ∃ a, ¬ (d ≤ a) ∧ deg0 < a

-- /-! 19. Join respects degrees (well-definedness on representatives). -/
-- /-- English: If `f ≡ᵀ f'` and `g ≡ᵀ g'`, then `⟦f⟧ ⩔ ⟦g⟧ = ⟦f'⟧ ⩔ ⟦g'⟧`. -/
-- axiom join_welldefined {f f' g g' : ℕ →. ℕ} :
--   AntisymmRel TuringReducible f f' →
--   AntisymmRel TuringReducible g g' →
--   (⟦f⟧ : TuringDegree) ⩔ ⟦g⟧ = ⟦f'⟧ ⩔ ⟦g'⟧

-- /-! 20. Join computes upper bounds (monotonicity in each argument). -/
-- /-- English: If `a₁ ≤ a₂` then `a₁ ⩔ b ≤ a₂ ⩔ b`, and similarly on the right. -/
-- axiom sup_mono_left  {a₁ a₂ b : TuringDegree} : a₁ ≤ a₂ → a₁ ⩔ b ≤ a₂ ⩔ b
-- axiom sup_mono_right {a b₁ b₂ : TuringDegree} : b₁ ≤ b₂ → a ⩔ b₁ ≤ a ⩔ b₂

end
