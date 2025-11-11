import Mathlib.Tactic.Linarith

namespace MyProject.Thm.Grind

/- ## Pattern Matching -/

example (n : Nat) : (match n with
  | 0   => 2
  | k+1 => k + 3) > 0 := by
  grind

example (x y : Nat) : (match x, y with
  | 0, 0     => 1
  | 0, n+1   => n + 2
  | m+1, 0   => m + 2
  | m+1, n+1 => m + n + 3) > 0 := by
  grind

example (x : Option Nat) : (match x with
  | none   => 5
  | some n => n + 5) ≥ 5 := by
  grind

example (l : List Nat) : (match l with
  | []    => 1
  | h::_ => h + 2) > 0 := by
  grind

example (b : Bool) (x y : Nat) : (if b then x + 1 else y + 1) > 0 := by
  grind

/- ## Linear Arithmetic -/

example (a b c : Int) :
    a + b = 5 → b + c = 7 → a + c = 6
    → a = 2 ∧ b = 3 ∧ c = 4 := by
  intro h1 h2 h3
  constructor
  · linarith
  constructor
  · linarith
  · linarith

example (x y z : Nat) :
    x + y + z = 10
    → 2*x ≤ y + z
    → y ≤ x + z
    → z ≤ x + y
    → x ≤ 5 := by
  intro h1 h2 h3 h4
  linarith

example (p q : Int) :
    p + q = 10
    → p ≥ 3
    → q ≥ 2
    → p + 2*q ≤ 20 := by
  intro h1 h2 h3
  linarith

/- ## Propositional Logic -/

example (P Q R : Prop) :
    (P → Q) → (Q → R) → P → R := by
  grind

example (P Q : Prop) :
    ¬(P ∧ Q) → (¬P ∨ ¬Q) := by
  grind

example (P Q : Prop) :
    (P → Q) → (¬Q → ¬P) := by
  grind

example (P Q R : Prop) :
    P ∧ (Q ∨ R) → (P ∧ Q) ∨ (P ∧ R) := by
  grind

/- ## Equality and Congruence -/

example (f : Nat → Nat) (x y : Nat) :
    x = y → f x = f y := by
  grind

example (f g : Nat → Nat) (x : Nat) :
    (∀ y, f y = g y) → f (f x) = g (g x) := by
  grind

example (a b c : Nat) :
    a = b → b = c → a = c := by
  grind

example (x y : Nat) :
    x = y → y = x := by
  grind

/- ## Combined Reasoning -/

example (n : Nat) (h : n > 0) :
    (match n with
    | 0   => 0  -- This case is impossible given h
    | k+1 => k + 1) > 0 := by
  grind

example (x : Option Nat) (y : Nat) :
    y ≥ 10 →
    (match x with
    | none   => y
    | some n => n + y) ≥ 10 := by
  grind

example (x y : Nat) (b : Bool) :
    x < y →
    (if b then x else x + 1) < y + 2 := by
  grind

example (n : Nat) :
    (match n % 2 with
    | 0 => 2
    | _ => 3) > 1 := by
  grind

end MyProject.Thm.Grind
