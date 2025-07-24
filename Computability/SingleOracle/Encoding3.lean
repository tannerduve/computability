import Computability.SingleOracle.Encoding2
open Nat
-- def list_append : ℕ→ℕ→ℕ := fun l x => (Encodable.decode l).getD 2
@[simp] abbrev Nat.l (n:ℕ) := n.unpair.1
@[simp] abbrev Nat.r (n:ℕ) := n.unpair.2
def empty_list : ℕ := Nat.pair 0 0
def list_append (list ele:ℕ):ℕ:=Nat.pair (list.l+1) (Nat.pair list.r ele)
def list_get_aux (index list:ℕ):ℕ:=
match index with
| 0 => list.r
| Nat.succ prev_index => (list_get_aux prev_index list).r
def list_get (index list:ℕ):ℕ:=(list_get_aux index list).l
def Nat.tail (list:ℕ):ℕ:=list_get list.l list

def zero_ef (x:ℕ):ℕ:=list_append x 0
def succ_ef (x:ℕ):ℕ:=list_append x x.tail.succ
def left_ef (x:ℕ):ℕ:=list_append x x.tail.l
def right_ef (x:ℕ):ℕ:=list_append x x.tail.r

theorem succ_eff : succ_ef x = list_append x x.tail.succ := by exact rfl

namespace Nat.RecursiveIn.Code
-- def evaln_ef (O:ℕ→ℕ):ℕ→ℕ→ℕ→Option ℕ
def evaln_ef (O:ℕ→ℕ):ℕ→Code→ℕ→Option ℕ
| 0, _ => fun _ => Option.none
| k+1, zero   => fun n => do guard (n≤k); return (zero_ef n)
| k+1, succ   => fun n => do guard (n≤k); return (succ_ef n)
| k+1, left   => fun n => do guard (n≤k); return (left_ef n)
| k+1, right  => fun n => do guard (n≤k); return (right_ef n)
| k+1, oracle => fun n => do guard (n≤k); pure (O n)
| k+1, pair cf cg => fun n => do
  guard (n ≤ k)
  Nat.pair <$> evaln O (k+1) cf n <*> evaln O (k+1) cg n
| k+1, comp cf cg => fun n => do
  guard (n ≤ k)
  let x ← evaln O (k+1) cg n
  evaln O (k+1) cf x
| k+1, prec cf cg => fun n => do
  guard (n ≤ k)
  n.unpaired fun a n =>
    n.casesOn (evaln O (k+1) cf a) fun y => do
      let i ← evaln O k (prec cf cg) (Nat.pair a y)
      evaln O (k+1) cg (Nat.pair a (Nat.pair y i))
| k+1, rfind' cf => fun n => do
  guard (n ≤ k)
  n.unpaired fun a m => do
    let x ← evaln O (k + 1) cf (Nat.pair a m)
    if x = 0 then
      pure m
    else
      evaln O k (rfind' cf) (Nat.pair a (m + 1))

theorem eq_imp_guardeq {f g:ℕ→ℕ} {k:ℕ} : f=g → (fun x => do guard (x≤k); return (f x):ℕ→Option ℕ) = (fun x => do guard (x≤k); return (g x)) := by
  simp
  intro h
  rw [h]

theorem evaln_ef_eq_eval : (fun x => (evaln_ef O s n x).bind (Option.some ∘ Nat.tail)) = fun x => evaln O s n x := by
  cases s with
  | zero =>
    simp [evaln_ef, evaln]
  | succ n =>
    expose_names
    induction n_1 with
    | zero =>
      have :
        ∀ {k k₂ n x : ℕ} {o₁ o₂ : Option ℕ},
          k ≤ k₂ → (x ∈ o₁ → x ∈ o₂) →
            x ∈ do { guard (n ≤ k); o₁ } → x ∈ do { guard (n ≤ k₂); o₂ } := by
        simp only [Option.mem_def, bind, Option.bind_eq_some, Option.guard_eq_some', exists_and_left,
          exists_const, and_imp]
        introv h h₁ h₂ h₃
        exact ⟨le_trans h₂ h, h₁ h₃⟩
      -- simp? at h ⊢ says simp only [Option.mem_def] at h ⊢
      simp only [evaln_ef, evaln]
      rw [eq_imp_guardeq]
      ·
      refine this
      apply?
      -- simp [bind]
      simp [guard_eq_some']
      unfold zero_ef
      unfold list_append
      exact?
    | succ =>
      simp [evaln_ef, evaln]
    | left => simp [evaln_ef]
    | right => sorry
    | oracle => sorry
    | pair _ _ => sorry
    | comp _ _ => sorry
    | prec _ _ => sorry
    | rfind' _ => sorry
    -- simp [evaln_ef]
    simp
