import MyProject

/-!
# Core Tests

Unit tests for core functionality.
-/

namespace Test.Core

open MyProject

-- Test helper to run assertions
def assert (condition : Bool) (message : String) : IO Unit := do
  if not condition then
    throw (IO.userError s!"Test failed: {message}")

def testDouble : IO Unit := do
  assert (double 0 == 0) "Double of 0 should be 0"
  assert (double 5 == 10) "Double of 5 should be 10"
  assert (double 100 == 200) "Double of 100 should be 200"
  IO.println "PASS: All double tests passed"

def testAdd : IO Unit := do
  assert (add 2 3 == 5) "2 + 3 should be 5"
  assert (add 0 10 == 10) "0 + 10 should be 10"
  assert (add 100 200 == 300) "100 + 200 should be 300"
  IO.println "PASS: All add tests passed"

def runTests : IO Unit := do
  IO.println "Running Core Tests"
  IO.println "=================="
  testDouble
  testAdd
  IO.println ""

end Test.Core
