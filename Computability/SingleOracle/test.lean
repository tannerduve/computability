import Computability.SingleOracle.RecursiveInTheorems
-- import Computability.SingleOracle.Encoding
import Mathlib.Computability.Reduce
import Mathlib.Computability.Halting

import Mathlib.Data.PFun

open Computability
open Classical

def evalo_index : (ℕ→ℕ→ℕ) := fun e x =>

theorem evalo_index : evalo O evalo_index $ (Nat.pair e x) = evalo e x := by sorry
