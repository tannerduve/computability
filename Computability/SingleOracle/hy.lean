-- import Computability.SingleOracle.Encoding2
-- -- import Computability.SingleOracle.Encoding
-- -- import Computability.SingleOracle.Oracle2
-- -- some theorems that'd be nice:
-- -- 1. K_0 =_T K
-- -- 2. characterising the c.e. sets as domains of partial functions is equivalent to characterising them as ranges of partial functions
-- -- 3. Non-empty c.e. sets are totally generatable
-- -- 4. the non constructive thm: Theorem 5.11: see /mnt/Q/Mathematics/LaTeX/Textbooks/ToRFaEC.pdf
-- -- there exists an infinite set having no infinite recursively enumerable subset. (problem 5.8 ToRFaEC)

-- -- THEOREM 10.3.5 of /mnt/Q/Mathematics/Textbooks/Computability/Computability Theory [Cooper] (2004).pdf

-- open Nat.RecursiveIn.Code
-- open Classical

-- noncomputable
-- def jumpConst (O:ℕ→ℕ) : (ℕ→Option ℕ) := fun x => (eval O x x).toOption
-- theorem contra : @RecursiveIn O ℕ (Option ℕ) _ _ (jumpConst O) := by
--     apply?
--     exact?
