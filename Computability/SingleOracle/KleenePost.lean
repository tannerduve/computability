import Computability.SingleOracle.Jump
import Computability.SingleOracle.SetOracles

open Nat.RecursiveIn.Code
open Computability

-- def D : ℕ→Finset ℕ := fun a => {x | (BSMem (Nat.pair a x))=1}
-- def D : ℕ→Set ℕ := fun a => {x | (BSMem (Nat.pair a x))=1}

-- We define interpretations of naturals as finite strings on the alphabet {0,1}.
-- (b,l) is interpreted as the string of length l, whose sequence matches with the binary representation of b.
/-- `BSMem (a,x) = [x ∈ Dₐ]` (iversion brackets) -/
def BSMem : ℕ → ℕ := fun xa => if Nat.testBit xa.r xa.l.l then 1 else 0
#eval BSMem (Nat.pair 3 0b01000)
theorem Nat.Primrec.BSMem_prim : Nat.Primrec BSMem := by sorry
def BSUnion : ℕ → ℕ := fun bl1bl2 => Nat.pair (Nat.lor bl1bl2.l.l bl1bl2.r.l) (Nat.max bl1bl2.l.r bl1bl2.r.r)
theorem Nat.Primrec.BSUnion_prim : Nat.Primrec BSUnion := by sorry
def DSize : ℕ → ℕ
| 0     => 0
| (n+1) => (n+1)&&&1 + DSize ((n+1)/2)
theorem Nat.Primrec.DSize_prim : Nat.Primrec DSize := by sorry

partial def KP54 : ℕ → ℕ := fun s =>
  let _ := s.div2

  if s = 0 then Nat.pair 0 0
  else if s % 2 = 0 then
    let _ := DSize (KP54 (s - 1)).r
    -- ask ∅' if there exists a n s.t. a:=BSUnion n (KP54 s-1).l satisfies (eval (D a) i n).Dom.
    -- if so then return (a, )
    Nat.pair 0 0
  else Nat.pair 0 0
/-
`KP54(s)=(a,b)` where `D a, D b` correspond to sets `A` and `B` at stage `s`.
We note that:
 · by stage 2n,   `χ_B(n)` is bound to be defined.
 · by stage 2n+1, `χ_A(n)` is bound to be defined.
-/

-- private def A := {x | x ∈ D (KP54 (2*x+1)).l}
-- private def B := {x | x ∈ D (KP54 (2*x)).r}
private def A := {x | BSMem (Nat.pair x (KP54 (2*x+1)).l) = 1}
private def B := {x | BSMem (Nat.pair x (KP54 (2*x)).r)   = 1}

private theorem R (i:ℕ) : evalSet A i ≠ χ B := by
  simp
  induction' (decodeCode i)
  · intro contra
    simp [eval, B, BSMem, Nat.testBit, HShiftRight.hShiftRight, pure] at contra
    sorry
  all_goals sorry

private theorem S (i:ℕ) : evalSet B i ≠ χ A := by sorry

theorem ex_incomparable_sets : ∃ A B:Set ℕ, A|ᵀB := by
  use A
  use B
  constructor
  · change ¬SetTuringReducible A B
    intro h
    unfold SetTuringReducible at h
    apply exists_code_nat.mp at h
    rcases h with ⟨c,hc⟩
    have contrad := S c
    exact contrad hc
  · change ¬SetTuringReducible B A
    intro h
    unfold SetTuringReducible at h
    apply exists_code_nat.mp at h
    rcases h with ⟨c,hc⟩
    have contrad := R c
    exact contrad hc
