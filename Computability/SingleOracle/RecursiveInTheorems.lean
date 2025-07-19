import Computability.SingleOracle.Encoding
import Mathlib.Data.PFun

open Computability
open Classical

@[simp] lemma RecursiveIn.partCompTotal {O f:ℕ→.ℕ} {g:ℕ→ℕ} (h1: RecursiveIn O f) (h2: RecursiveIn O g) : (RecursiveIn O ↑(f∘g)) := by
  have h3 : (↑(f∘g):ℕ→.ℕ) = fun x => g x >>= (↑f:ℕ→.ℕ) := by
    funext xs
    simp
  rw [h3]
  exact comp h1 h2
@[simp] lemma RecursiveIn.totalComp {O:ℕ→.ℕ} {f g:ℕ→ℕ} (h1: RecursiveIn O f) (h2: RecursiveIn O g) : (RecursiveIn O ↑(f∘g)) := by
  have h3 : (↑(f∘g):ℕ→.ℕ) = fun x => g x >>= (↑f:ℕ→.ℕ) := by
    funext xs
    simp
  rw [h3]
  exact comp h1 h2
@[simp] lemma RecursiveIn.id {O:ℕ→.ℕ} : RecursiveIn O fun x => x := by apply of_primrec Nat.Primrec.id
@[simp] lemma RecursiveIn.someTotal (O:ℕ→.ℕ) (f:ℕ→ℕ) (h1: RecursiveIn O f): RecursiveIn O fun x => Part.some (f x) := by
  apply RecursiveIn.totalComp
  · exact h1
  · apply RecursiveIn.id


@[simp] def Nat.flatten := fun x => if x=0 then 0 else 1
@[simp] def Nat.flattenInv := fun x => if x=0 then 1 else 0

open Nat.Primrec in
theorem Nat.Primrec.flatten : Nat.Primrec Nat.flatten := by
  let construction := comp (prec zero (((const 1).comp left).comp left)) (pair zero .id)
  apply Nat.Primrec.of_eq
  · exact construction
  · simp
    intro n
    induction n with
    | zero => exact rfl
    | succ n _ => simp
open Nat.Primrec in
theorem Nat.Primrec.flattenInv : Nat.Primrec Nat.flattenInv := by
  let construction := comp (prec (const 1) (((zero).comp left).comp left)) (pair zero .id)
  apply Nat.Primrec.of_eq
  · exact construction
  · simp
    intro n
    induction n with
    | zero => exact rfl
    | succ n _ => simp

@[simp] lemma RecursiveIn.pair' (f g : ℕ→ℕ) : ((↑fun x ↦ Nat.pair (f x) (g x)):ℕ→.ℕ)= fun (x:ℕ) => (Nat.pair <$> (f x) <*> (g x)) := by
  simp [Seq.seq]
  funext xs
  simp
@[simp] lemma RecursiveIn.totalComp' {O:ℕ→.ℕ} {f g:ℕ→ℕ} (hf: RecursiveIn O f) (hg: RecursiveIn O g): (RecursiveIn O (fun x => (f (g x)):ℕ→ℕ) ) := by apply RecursiveIn.totalComp (hf) (hg)
@[simp] lemma RecursiveIn.totalComp₂ {O:ℕ→.ℕ} {f:ℕ→ℕ→ℕ} {g h:ℕ→ℕ} (hf: RecursiveIn O fun x => f x.unpair.1 x.unpair.2) (hg: RecursiveIn O g) (hh: RecursiveIn O h): (RecursiveIn O (fun x => (f (g x) (h x)):ℕ→ℕ) ) := by
  have main : (fun x => (f (g x) (h x)):ℕ→ℕ) = ((fun x => f x.unpair.1 x.unpair.2) ∘ (fun n ↦ Nat.pair (g n) (h n))) := by
    funext xs
    simp
  rw [main]
  apply RecursiveIn.totalComp
  · exact hf
  · rw [RecursiveIn.pair']
    apply RecursiveIn.pair hg hh

theorem RecursiveIn.ifz1 {O:ℕ→.ℕ} {c:ℕ→ℕ} (hc : RecursiveIn O c): RecursiveIn O (fun x => if (c x=0) then (a:ℕ) else (b:ℕ) : ℕ→ℕ) := by
  let construction := fun x =>
    Nat.add
    (Nat.mul b (Nat.flatten (c x)))
    (Nat.mul a (Nat.flattenInv (c x)))
  have consRecin : RecursiveIn O construction := by
    simp only [construction]
    apply RecursiveIn.totalComp₂
    · apply of_primrec Nat.Primrec.add
    · apply RecursiveIn.totalComp₂
      · apply of_primrec Nat.Primrec.mul
      · apply of_primrec (Nat.Primrec.const b)
      · apply RecursiveIn.totalComp'
        · exact of_primrec Nat.Primrec.flatten
        · exact hc
    · apply RecursiveIn.totalComp₂
      · apply of_primrec Nat.Primrec.mul
      · apply of_primrec (Nat.Primrec.const a)
      · apply RecursiveIn.totalComp'
        · exact of_primrec Nat.Primrec.flattenInv
        · exact hc
  have consEq: (fun x => if (c x=0) then (a:ℕ) else (b:ℕ) : ℕ→ℕ) = construction := by
    simp [construction]
    funext xs
    cases Classical.em (c xs = 0) with -- do i really need classical.em here?
      | inl h => simp [h]
      | inr h => simp [h]

  rw [consEq]
  exact consRecin


def evalo' (O:ℕ→.ℕ) : (ℕ→.ℕ) := fun y => (evalo O y.unpair.1 y.unpair.2)

variable {α : Type*} {β : Type*} {σ : Type*}
variable [Primcodable α] [Primcodable β] [Primcodable σ]
theorem Primrec.projection {f : α → β → σ} {a:α} (h:Primrec₂ f) : Primrec (f a) := by
  refine Primrec₂.comp h ?_ ?_
  · exact const a
  · exact Primrec.id
lemma Nat.Primrec.pair_proj : Nat.Primrec (Nat.pair x) := by
  refine Primrec.nat_iff.mp ?_
  apply Primrec.projection
  exact Primrec₂.natPair

theorem RecursiveIn.evaloRecInO' {f O:ℕ→.ℕ} (h:RecursiveIn O f) : RecursiveIn O (fun x => (f x) >>= (evalo' O)) := by
  simp
  refine comp ?_ h
  apply RecursiveIn.evalo_computable
theorem RecursiveIn.evalo_K_computable : RecursiveIn O (fun x ↦ evalo O x x) := by
  have h : (fun (x:ℕ) ↦ evalo O x x) = (fun (x:ℕ) => evalo O x.unpair.1 x.unpair.2) ∘ (fun x=>Nat.pair x x) := by
    funext xs
    simp only [Function.comp_apply, Nat.unpair_pair]
  rw [h]
  refine RecursiveIn.partCompTotal ?_ ?_
  exact RecursiveIn.evalo_computable
  exact RecursiveIn.of_primrec (Nat.Primrec.pair Nat.Primrec.id Nat.Primrec.id)

theorem RecursiveIn.ite {O:ℕ→.ℕ} {f g : ℕ→.ℕ} {c:ℕ→ℕ} (hc : RecursiveIn O c) (hf : RecursiveIn O f) (hg : RecursiveIn O g) : RecursiveIn O fun a => if (c a=0) then (f a) else (g a) := by
    have exists_index_for_f : ∃ c : ℕ, evalo O c = f := by exact (exists_codeN_rel O f).mp hf
    have exists_index_for_g : ∃ c : ℕ, evalo O c = g := by exact (exists_codeN_rel O g).mp hg
    rcases exists_index_for_f with ⟨index_f,index_f_is_f⟩
    rcases exists_index_for_g with ⟨index_g,index_g_is_g⟩

    have main2 : (fun a => if (c a=0) then (f a) else (g a)) = fun a => Nat.pair (if c a=0 then (index_f) else (index_g)) a >>= evalo' O := by
      funext xs
      cases Classical.em (c xs = 0) with
      | inl h =>
        simp [h, evalo']
        exact congrFun (_root_.id (Eq.symm index_f_is_f)) xs
      | inr h =>
        simp [h, evalo']
        exact congrFun (_root_.id (Eq.symm index_g_is_g)) xs
    rw [main2]


    apply RecursiveIn.evaloRecInO'
    apply RecursiveIn.someTotal

    rw [RecursiveIn.pair']

    apply RecursiveIn.pair
    · simp
      apply RecursiveIn.ifz1
      exact hc
    exact id


-- theorem RecursiveIn.dite {O:ℕ→ℕ} {c:ℕ→ℕ} {f :(a:ℕ)→(c a=0)→ℕ} {g:(a:ℕ)→¬(c a=0)→ℕ}
--   (hc : RecursiveIn O c)
--   (hf : (h:c a=0) → RecursiveIn O (f a h))
--   (hg : (h:¬(c a=0)) → RecursiveIn O (g a h)) :
--   RecursiveIn O fun a => if h:(c a=0) then (f a h a) else (g a h a) := by
--     have construction : (fun a => if h:(c a=0) then (f a h a) else (g a h a)) = (fun a => if h:(c a=0) then (f a h a) else (g a h a)) := by sorry
--   RecursiveIn O fun a => dite (c a=0) (fun h => f (cast (by (expose_names; exact False.elim h_1)) h) a) (g h a) := by sorry
