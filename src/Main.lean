import MyProject

/-!
# Main Entry Point

Executable entry point for the application.
-/

def main : IO UInt32 := do
  IO.println "MyProject Template"
  IO.println "=================="
  IO.println ""
  IO.println "This is a Lean 4 project template."
  IO.println "Customize this main function for your application."

  -- Example: Use some simple functions
  let x : MyProject.Qty := 10
  let y : MyProject.Qty := 5

  IO.println s!"x = {x}, y = {y}"
  IO.println s!"double({x}) = {MyProject.double x}"
  IO.println s!"add({x}, {y}) = {MyProject.add x y}"

  return 0
