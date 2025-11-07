/-
File: FiniteInjury.lean
Author: GitHub Copilot

A compact, reusable skeleton for formalizing finite-injury priority
arguments.  The development is intentionally abstract: it isolates the
core combinatorial fact used in finite-injury constructions and gives a
clean statement that "if every requirement only acts (injures) on any
coordinate eventually no more, then the stagewise approximation
stabilizes pointwise".  The usual priority argument then proceeds by
showing each requirement is injured only finitely often (by induction
on priority), which fits into this framework.

This file uses the (mathlib-style) libraries for finsets, fintypes and
classical choice.  It avoids committing to a specific computability
representation (or to a particular action/strategy), so it should be
easy to instantiate for specific constructions in the computability
library.
-/
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Basic
-- import Mathlib.Tactic
-- import Mathlib.Order.Basic
open Classical

variable {α : Type}

/-
We consider a stagewise approximation `f : ℕ → ℕ → α`, where
`f s x` is the value of the approximation at stage `s` on coordinate `x`.

There are finitely many requirements, indexed by `Fin n`.  At stage `s`
requirement `i : Fin n` may "act" on some coordinates; we model this
by a predicate `acts_on s i x`.
-/
section finite_injury
open Finset

variable {n : ℕ}

/- stagewise approximation: stage → coordinate → value -/
variable (f : ℕ → ℕ → α)

/- acts_on s i x: at stage s, requirement i acts on coordinate x -/
variable (acts_on : ℕ → Fin n → ℕ → Prop)

/- Changes in `f` exactly correspond to some requirement acting there. -/
variable (h_change_iff :
  ∀ (s x : ℕ), f (s+1) x ≠ f s x ↔ ∃ (i : Fin n), acts_on s i x)

/- Finite-injury hypothesis (in the "eventual" form):
    for every requirement `i` and coordinate `x` there is a stage `M`
    after which `i` never acts on `x` again.  This is the typical
    property one proves by induction on priority in a finite-injury
    construction. -/
axiom h_eventual :
  ∀ (i : Fin n) (x : ℕ), ∃ (M : ℕ), ∀ s, s ≥ M → ¬ acts_on s i x



/-
If every requirement acts only finitely often (expressed by
`h_eventual`), then each coordinate stabilizes: there is a stage `N`
after which the value at that coordinate does not change anymore.
-/
theorem finite_injury_pointwise_stabilize {n : ℕ} (x : ℕ) :
  ∃ (N : ℕ), ∀ s, s ≥ N → f s x = f N x := by
  -- For each requirement `i` pick a stage `M i` after which `i` never acts on `x`.
  let M : Fin n → ℕ := fun i => (zh_eventual i x).some
  have hM : ∀ i, ∀ s, s ≥ M i → ¬ acts_on s i x := by
    intro i s hs
    exact (h_eventual i x).some_spec s hs

  -- Take the maximum of these finitely many bounds; `Fin n` is finite,
  -- so `Finset.univ.sup` computes the max over the finite index set.
  let N := (Finset.univ : Finset (Fin n)).sup id M
  have hN_ge (i : Fin n) : N ≥ M i := by
    -- `sup` is an upper bound for each `M i`.
    have : M i ≤ (Finset.univ : Finset (Fin n)).sup id M := Finset.le_sup (by simp) i
    exact this

  -- For every stage s ≥ N, no requirement acts on x at stage s.
  have no_act_after : ∀ s, s ≥ N → (∀ i, ¬ acts_on s i x) := by
    intro s hs i
    apply hM i s (le_trans (hN_ge i) hs)

  -- Using the correspondence between changes and acts, deduce
  -- that for s ≥ N we have f (s+1) x = f s x. From that one gets
  -- full stabilization by a simple induction.
  have step_stable : ∀ s, s ≥ N → f (s+1) x = f s x := by
    intro s hs
    have : ¬ (∃ i, acts_on s i x) := by
      intro h; cases h with i hi; exact (no_act_after s hs i) hi
    simpa [h_change_iff] using (not_iff.mp (by
      convert (h_change_iff s x) ; simp [this])) -- unwrap the iff

  -- Now lift one-step stability to full stability from stage `N`.
  use N
  intro s hs
  -- proceed by induction on the difference `s - N`.
  have : ∀ t, t ≤ s - N → f (N + t) x = f N x := by
    intro t ht
    induction' t with t ih
    · simp
    · calc
        f (N + t + 1) x = f (N + t) x := by
          apply step_stable (N + t)
          simpa using Nat.le_add_right _ _
        _ = f N x := ih (by simpa using ht)
  -- instantiate with `t = s - N`
  have hdiff : s = N + (s - N) := by
    exact (Nat.add_sub_of_le hs).symm
  simpa [hdiff] using (this (s - N) (by simp))

end finite_injury
