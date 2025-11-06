/-!
# MyProject Types

Core type definitions for the project.
-/

namespace MyProject

abbrev Qty := Rat

-- Example enumeration
inductive Status where
  | pending
  | active
  | completed
  | failed
deriving Repr, DecidableEq

-- Example type class
class HasId (α : Type) where
  getId : α → String

end MyProject
