import MyProject.Types
import Mathlib.Tactic.Ring

/-!
# MyProject Core

Core functionality and business logic.
-/

namespace MyProject

/-- Double a quantity -/
def double (x : Qty) : Qty := x * 2

/-- Add two quantities -/
def add (x y : Qty) : Qty := x + y

-- Simple theorem: double of zero is zero
theorem double_zero : double 0 = 0 := by
  unfold double
  simp

-- Simple lemma: double is same as adding to itself
lemma double_eq_add_self (x : Qty) : double x = add x x := by
  unfold double add
  ring

-- Trivial theorem with trivial proof
theorem add_comm (x y : Qty) : add x y = add y x := by
  unfold add
  ring

end MyProject
