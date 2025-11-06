import MyProject.Types
import Std.Data.HashMap

/-!
# MyProject Utils

Utility functions and helpers.
-/

namespace MyProject.Utils

-- Example: String utilities
def truncate (s : String) (maxLen : Nat) : String :=
  if s.length ≤ maxLen then s
  else s.take maxLen ++ "..."

def isValidId (id : String) : Bool :=
  id.length > 0 && id.length ≤ 32 && id.all Char.isAlphanum

-- Example: Collection helpers
def findById {α : Type} [HasId α] (items : List α) (id : String) : Option α :=
  items.find? (fun item => HasId.getId item == id)

def groupBy {α β : Type} [BEq β] [Hashable β]
    (f : α → β) (items : List α) : Std.HashMap β (List α) :=
  items.foldl (fun acc item =>
    let key := f item
    let existing := acc.get? key |>.getD []
    acc.insert key (item :: existing)
  ) {}

-- Example: Result type for operations
inductive OpResult (α : Type) where
  | success : α → OpResult α
  | failure : String → OpResult α
deriving Repr

namespace OpResult

def isSuccess {α : Type} : OpResult α → Bool
  | success _ => true
  | failure _ => false

def map {α β : Type} (f : α → β) : OpResult α → OpResult β
  | success a => success (f a)
  | failure msg => failure msg

def bind {α β : Type} (f : α → OpResult β) : OpResult α → OpResult β
  | success a => f a
  | failure msg => failure msg

end OpResult

end MyProject.Utils
