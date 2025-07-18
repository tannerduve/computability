import Computability.SingleOracle.Jump

def SetRecursiveIn (O:Set ℕ) (A:Set ℕ): Prop :=
  RecursiveIn (fun x => if x∈O then 1 else 0) (fun x => if x∈A then 1 else 0)

noncomputable def evaloSet (O : Set ℕ) : codeo → ℕ →. ℕ := evalo (fun x => if x∈O then 1 else 0)

def SetK0 (A:Set ℕ) := {ex:ℕ | (evaloSet A ex.unpair.1 ex.unpair.2).Dom}
def SetK (A:Set ℕ) := {x:ℕ | (evaloSet A x x).Dom}
