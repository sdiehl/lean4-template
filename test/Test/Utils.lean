import MyProject
import MyProject.Utils

/-!
# Utils Tests

Unit tests for utility functions.
-/

namespace Test.Utils

open MyProject
open MyProject.Utils

def assert (condition : Bool) (message : String) : IO Unit := do
  if not condition then
    throw (IO.userError s!"Test failed: {message}")

def testTruncate : IO Unit := do
  let shortStr := "hello"
  assert (truncate shortStr 10 == "hello")
    "Short string should not be truncated"

  let longStr := "This is a very long string that should be truncated"
  let truncated := truncate longStr 20
  assert (truncated == "This is a very long ...")
    s!"String should be truncated to 20 chars + '...', got: {truncated}"

  IO.println "PASS: All truncate tests passed"

def testIsValidId : IO Unit := do
  -- Valid IDs
  assert (isValidId "ABC123") "Alphanumeric ID should be valid"
  assert (isValidId "test") "Simple text ID should be valid"

  -- Invalid IDs
  assert (not (isValidId "")) "Empty ID should be invalid"
  assert (not (isValidId "test-id")) "ID with hyphen should be invalid"
  assert (not (isValidId "test_id")) "ID with underscore should be invalid"

  let longId := String.mk (List.replicate 40 'A')
  assert (not (isValidId longId)) "ID longer than 32 chars should be invalid"

  IO.println "PASS: All ID validation tests passed"

def testOpResult : IO Unit := do
  -- Test success case
  let success : OpResult Nat := OpResult.success 42
  assert success.isSuccess "Success should be identified correctly"

  -- Test failure case
  let failure : OpResult Nat := OpResult.failure "Error occurred"
  assert (not failure.isSuccess) "Failure should be identified correctly"

  -- Test map
  let mapped := success.map (· * 2)
  match mapped with
  | OpResult.success n =>
    assert (n == 84) s!"Mapped value should be 84, got {n}"
  | OpResult.failure _ =>
    throw (IO.userError "Map failed on success value")


  IO.println "PASS: All OpResult tests passed"

def runTests : IO Unit := do
  IO.println "Running Utils Tests"
  IO.println "==================="
  testTruncate
  testIsValidId
  testOpResult
  IO.println ""

end Test.Utils
