import MyProject.Core
import MyProject.Types
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# Algebraic Theorems

Theorems about algebraic properties of the types and operations.
-/

namespace MyProject.Thm

-- Since Qty is Rat, we can prove field properties

-- Theorem: multiplication distributes over addition for Qty
theorem mul_distrib (x y z : Qty) : x * (y + z) = x * y + x * z := by
  ring

-- Theorem: non-zero elements have multiplicative inverse
theorem inv_exists (x : Qty) (h : x ≠ 0) : ∃ y : Qty, x * y = 1 := by
  use x⁻¹
  field_simp

-- Theorem: status has decidable equality
example (s1 s2 : Status) : Decidable (s1 = s2) := by
  infer_instance

end MyProject.Thm
