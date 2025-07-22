import Computability.SingleOracle.Encoding2
import Mathlib.Data.PFun

open Computability
open Classical

open Nat.RecursiveIn.Code


@[simp] lemma Nat.RecursiveIn.partCompTotal {O:ℕ→ℕ} {f:ℕ→.ℕ} {g:ℕ→ℕ} (h1: Nat.RecursiveIn O f) (h2: Nat.RecursiveIn O g) : (Nat.RecursiveIn O ↑(f∘g)) := by
  have h3 : (↑(f∘g):ℕ→.ℕ) = fun x => g x >>= (↑f:ℕ→.ℕ) := by
    funext xs
    simp only [Function.comp_apply, Part.coe_some, Part.bind_eq_bind, Part.bind_some]
  rw [h3]
  exact comp h1 h2
@[simp] lemma Nat.RecursiveIn.totalComp {O:ℕ→ℕ} {f g:ℕ→ℕ} (h1: Nat.RecursiveIn O f) (h2: Nat.RecursiveIn O g) : (Nat.RecursiveIn O ↑(f∘g)) := by
  have h3 : (↑(f∘g):ℕ→.ℕ) = fun x => g x >>= (↑f:ℕ→.ℕ) := by
    funext xs
    simp only [PFun.coe_val, Function.comp_apply, Part.coe_some, Part.bind_eq_bind, Part.bind_some]
  rw [h3]
  exact comp h1 h2
@[simp] lemma Nat.RecursiveIn.id {O:ℕ→ℕ} : Nat.RecursiveIn O fun x => x := by apply of_primrec Nat.Primrec.id
@[simp] lemma Nat.RecursiveIn.someTotal (O:ℕ→ℕ) (f:ℕ→ℕ) (h1: Nat.RecursiveIn O f): Nat.RecursiveIn O fun x => Part.some (f x) := by
  apply Nat.RecursiveIn.totalComp
  · exact h1
  · apply Nat.RecursiveIn.id


@[simp] def Nat.flatten := fun x => if x=0 then 0 else 1
@[simp] def Nat.flattenInv := fun x => if x=0 then 1 else 0

open Nat.Primrec in
theorem Nat.Primrec.flatten : Nat.Primrec Nat.flatten := by
  let construction := comp (prec zero (((const 1).comp left).comp left)) (pair zero .id)
  apply Nat.Primrec.of_eq
  · exact construction
  · simp only [unpaired, id_eq, unpair_pair, Nat.flatten]
    intro n
    induction n with
    | zero => exact rfl
    | succ n _ => simp only [Nat.add_eq_zero, one_ne_zero, and_false, ↓reduceIte]
open Nat.Primrec in
theorem Nat.Primrec.flattenInv : Nat.Primrec Nat.flattenInv := by
  let construction := comp (prec (const 1) (((zero).comp left).comp left)) (pair zero .id)
  apply Nat.Primrec.of_eq
  · exact construction
  · simp only [unpaired, id_eq, unpair_pair, Nat.flattenInv]
    intro n
    induction n with
    | zero => exact rfl
    | succ n _ => simp only [Nat.add_eq_zero, one_ne_zero, and_false, ↓reduceIte]

@[simp] lemma Nat.RecursiveIn.pair' (f g : ℕ→ℕ) : ((↑fun x ↦ Nat.pair (f x) (g x)):ℕ→.ℕ)= fun (x:ℕ) => (Nat.pair <$> (f x) <*> (g x)) := by
  simp [Seq.seq]
  funext xs
  simp only [PFun.coe_val]
@[simp] lemma Nat.RecursiveIn.totalComp' {O:ℕ→ℕ} {f g:ℕ→ℕ} (hf: Nat.RecursiveIn O f) (hg: Nat.RecursiveIn O g): (Nat.RecursiveIn O (fun x => (f (g x)):ℕ→ℕ) ) := by apply Nat.RecursiveIn.totalComp (hf) (hg)
@[simp] lemma Nat.RecursiveIn.comp₂ {O:ℕ→ℕ} {f:ℕ→ℕ→.ℕ} {g h:ℕ→ℕ} (hf: Nat.RecursiveIn O fun x => f x.unpair.1 x.unpair.2) (hg: Nat.RecursiveIn O g) (hh: Nat.RecursiveIn O h): (Nat.RecursiveIn O (fun x => (f (g x) (h x))) ) := by
  have main : (fun x => (f (g x) (h x))) = ((fun x => f x.unpair.1 x.unpair.2) ∘ (fun n ↦ Nat.pair (g n) (h n))) := by
    funext xs
    simp only [Function.comp_apply, unpair_pair]
  rw [main]
  refine partCompTotal hf ?_
  · rw [Nat.RecursiveIn.pair']
    apply Nat.RecursiveIn.pair hg hh
@[simp] lemma Nat.RecursiveIn.totalComp₂ {O:ℕ→ℕ} {f:ℕ→ℕ→ℕ} {g h:ℕ→ℕ} (hf: Nat.RecursiveIn O fun x => f x.unpair.1 x.unpair.2) (hg: Nat.RecursiveIn O g) (hh: Nat.RecursiveIn O h): (Nat.RecursiveIn O (fun x => (f (g x) (h x)):ℕ→ℕ) ) := by
  have main : (fun x => (f (g x) (h x)):ℕ→ℕ) = ((fun x => f x.unpair.1 x.unpair.2) ∘ (fun n ↦ Nat.pair (g n) (h n))) := by
    funext xs
    simp only [Function.comp_apply, Nat.unpair_pair]
  rw [main]
  apply Nat.RecursiveIn.totalComp
  · exact hf
  · rw [Nat.RecursiveIn.pair']
    apply Nat.RecursiveIn.pair hg hh

theorem Nat.RecursiveIn.ifz1 {O:ℕ→ℕ} {c:ℕ→ℕ} (hc : Nat.RecursiveIn O c): Nat.RecursiveIn O (fun x => if (c x=0) then (a:ℕ) else (b:ℕ) : ℕ→ℕ) := by
  let construction := fun x =>
    Nat.add
    (Nat.mul b (Nat.flatten (c x)))
    (Nat.mul a (Nat.flattenInv (c x)))
  have consRecin : Nat.RecursiveIn O construction := by
    simp only [construction]
    apply Nat.RecursiveIn.totalComp₂
    · apply of_primrec Nat.Primrec.add
    · apply Nat.RecursiveIn.totalComp₂
      · apply of_primrec Nat.Primrec.mul
      · apply of_primrec (Nat.Primrec.const b)
      · apply Nat.RecursiveIn.totalComp'
        · exact of_primrec Nat.Primrec.flatten
        · exact hc
    · apply Nat.RecursiveIn.totalComp₂
      · apply of_primrec Nat.Primrec.mul
      · apply of_primrec (Nat.Primrec.const a)
      · apply Nat.RecursiveIn.totalComp'
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


def Nat.RecursiveIn.Code.eval' (O:ℕ→ℕ) : (ℕ→.ℕ) := fun y => (eval O) (y.unpair.1) (y.unpair.2)
-- def Nat.ComputableIn (O f : ℕ->ℕ) := Nat.RecursiveIn O f
theorem RecursiveIn.eval_rec {O} : RecursiveIn O (eval' O) := by exact eval_part
theorem Nat.RecursiveIn.eval_rec {O} : Nat.RecursiveIn O (eval' O) := by exact RecursiveIn.nat_iff.mp _root_.RecursiveIn.eval_rec

theorem Nat.RecursiveIn.evalRecInO' {O} {f:ℕ→.ℕ} (h:Nat.RecursiveIn O f) : Nat.RecursiveIn O (fun x => (f x) >>= (eval' O)) := by
  simp only [Part.bind_eq_bind]
  refine comp ?_ h
  apply Nat.RecursiveIn.eval_rec
theorem Nat.RecursiveIn.eval_K_computable : Nat.RecursiveIn O (fun x ↦ eval O x x) := by
  have h : (fun (x:ℕ) ↦ eval O x x) = (fun (x:ℕ) => eval O x.unpair.1 x.unpair.2) ∘ (fun x=>Nat.pair x x) := by
    funext xs
    simp only [Function.comp_apply, Nat.unpair_pair]
  rw [h]
  refine Nat.RecursiveIn.partCompTotal ?_ ?_
  exact Nat.RecursiveIn.eval_rec
  exact Nat.RecursiveIn.of_primrec (Nat.Primrec.pair Nat.Primrec.id Nat.Primrec.id)

theorem exists_code_nat (O : ℕ → ℕ) (f : ℕ →. ℕ) : Nat.RecursiveIn O f ↔ ∃ c : ℕ , eval O c = f := by
  have h {f : ℕ →. ℕ} : Nat.RecursiveIn O f ↔ ∃ c : Nat.RecursiveIn.Code, eval O c = f := by exact
    exists_code
  constructor
  · intro h2
    obtain ⟨c, h3⟩ := h.mp h2
    use c.encodeCode
    simp only [decodeCode_encodeCode]
    exact h3
  · intro h2
    obtain ⟨c, h3⟩ := h2
    have h5: (∃ c:Nat.RecursiveIn.Code, eval O c = f) := by
      use decodeCode c
    exact exists_code.mpr h5



-- theorem smn_calc : ∃ f : ℕ → ℕ, ComputableIn O f ∧ ∀ c n random:ℕ, eval O (f ex) random = eval O ex.unpair.1 ex.unpair.2 :=
--   by
--     simp
  -- ⟨sorry, PrimrecIn₂.to_compIn curry_prim, eval_curry⟩


  -- ⟨curry, PrimrecIn₂.to_compIn curry_prim, eval_curry⟩

theorem Nat.RecursiveIn.ite {O:ℕ→ℕ} {f g : ℕ→.ℕ} {c:ℕ→ℕ} (hc : Nat.RecursiveIn O c) (hf : Nat.RecursiveIn O f) (hg : Nat.RecursiveIn O g) : Nat.RecursiveIn O fun a => if (c a=0) then (f a) else (g a) := by
    have exists_index_for_f : ∃ c : ℕ, eval O c = f := by exact (exists_code_nat O f).mp hf
    have exists_index_for_g : ∃ c : ℕ, eval O c = g := by exact (exists_code_nat O g).mp hg
    rcases exists_index_for_f with ⟨index_f,index_f_is_f⟩
    rcases exists_index_for_g with ⟨index_g,index_g_is_g⟩

    have main2 : (fun a => if (c a=0) then (f a) else (g a)) = fun a => Nat.pair (if c a=0 then (index_f) else (index_g)) a >>= eval' O := by
      funext xs
      cases Classical.em (c xs = 0) with
      | inl h =>
        simp only [h, ↓reduceIte, Part.coe_some, Part.bind_eq_bind, Part.bind_some, eval', Nat.unpair_pair]
        exact congrFun (_root_.id (Eq.symm index_f_is_f)) xs
      | inr h =>
        simp only [h, ↓reduceIte, Part.coe_some, Part.bind_eq_bind, Part.bind_some, eval', Nat.unpair_pair]
        exact congrFun (_root_.id (Eq.symm index_g_is_g)) xs
    rw [main2]


    apply Nat.RecursiveIn.evalRecInO'
    apply Nat.RecursiveIn.someTotal

    rw [Nat.RecursiveIn.pair']

    apply Nat.RecursiveIn.pair
    · simp only [Part.coe_some]
      apply Nat.RecursiveIn.ifz1
      exact hc
    exact id
