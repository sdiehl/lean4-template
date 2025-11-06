import MyProject.Core
import Mathlib.Tactic.Linarith

/-!
# Basic Theorems

Basic theorems about the core functions.
-/

namespace MyProject.Thm

-- Theorem: double is monotonic
theorem double_mono {x y : Qty} (h : x ≤ y) : double x ≤ double y := by
  unfold double
  linarith

-- Theorem: add is associative
theorem add_assoc (x y z : Qty) : add (add x y) z = add x (add y z) := by
  unfold add
  ring

-- Theorem: zero is identity for add
theorem add_zero (x : Qty) : add x 0 = x := by
  unfold add
  simp

theorem zero_add (x : Qty) : add 0 x = x := by
  unfold add
  simp

-- Theorem: double distributes over add
theorem double_add (x y : Qty) : double (add x y) = add (double x) (double y) := by
  unfold double add
  ring

end MyProject.Thm