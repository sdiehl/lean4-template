import Lake
open Lake DSL

package MyProject where
  -- Package configuration options
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,  -- pretty-prints `fun a ↦ b`
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩
  ]

-- Dependencies
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.24.0"

require batteries from git
  "https://github.com/leanprover-community/batteries" @ "v4.24.0"


-- Main library
@[default_target]
lean_lib MyProject where
  srcDir := "src"

-- Test library
lean_lib Test where
  srcDir := "test"

-- Main executable (example)
@[default_target]
lean_exe myproject where
  root := `Main
  srcDir := "src"

-- Test executable
@[default_target]
lean_exe tests where
  root := `Test.Main
  srcDir := "test"

-- Test runner script
@[test_driver]
script test do
  let proc ← IO.Process.spawn {
    cmd := ".lake/build/bin/tests"
  }
  let exitCode ← proc.wait
  return if exitCode = 0 then 0 else 1

-- Check that MyProject.Thm imports all theorem modules
script checkThm do
  let thm ← IO.FS.readFile ⟨"src/MyProject/Thm.lean"⟩
  let thmDir ← System.FilePath.readDir ⟨"src/MyProject/Thm/"⟩
  for entry in thmDir.toList do
    let fn := entry.fileName
    if fn.endsWith ".lean" then
      let moduleName := fn.dropRight 5
      let importLine := s!"import MyProject.Thm.{moduleName}"
      if thm.replace importLine "" == thm then
        IO.println s!"ERROR: MyProject.Thm does not import MyProject/Thm/{fn}"
        return 1
  IO.println "PASS: All theorem modules are imported"
  return 0

-- Module size linter (from CLAUDE.md conventions)
script checkSize do
  let mut hasViolation := false

  let checkFiles (dirPath : String) : IO Bool := do
    let dir ← System.FilePath.readDir ⟨dirPath⟩
    let mut violation := false
    for entry in dir.toList do
      if entry.fileName.endsWith ".lean" then
        let fullPath : System.FilePath := ⟨dirPath⟩ / entry.fileName
        let content ← IO.FS.readFile fullPath
        let lines := content.splitOn "\n"
        if lines.length > 900 then
          IO.println s!"ERROR: {fullPath} has {lines.length} lines (max 900)"
          violation := true
    return violation

  let v1 ← checkFiles "src"
  hasViolation := hasViolation || v1

  let v2 ← checkFiles "test"
  hasViolation := hasViolation || v2

  if not hasViolation then
    IO.println "PASS: All modules are within 900 line limit"

  return if hasViolation then 1 else 0

-- Lint driver that runs all checks
@[lint_driver]
script lint do
  IO.println "Running project lint checks..."
  IO.println "========================"

  let mut exitCode : Nat := 0

  -- Check theorem imports
  IO.println "\n[1/2] Checking theorem imports..."
  let thmPath : System.FilePath := ⟨"src/MyProject/Thm/"⟩
  if ← thmPath.pathExists then
    let thm ← IO.FS.readFile ⟨"src/MyProject/Thm.lean"⟩
    let thmDir ← System.FilePath.readDir thmPath
    for entry in thmDir.toList do
      let fn := entry.fileName
      if fn.endsWith ".lean" then
        let moduleName := fn.dropRight 5
        let importLine := s!"import MyProject.Thm.{moduleName}"
        if thm.replace importLine "" == thm then
          IO.println s!"ERROR: MyProject.Thm does not import MyProject/Thm/{fn}"
          exitCode := 1

  -- Check module sizes
  IO.println "\n[2/2] Checking module sizes (max 900 lines)..."
  let checkFiles (dirPath : String) : IO Bool := do
    if ← System.FilePath.pathExists ⟨dirPath⟩ then
      let dir ← System.FilePath.readDir ⟨dirPath⟩
      let mut violation := false
      for entry in dir.toList do
        if entry.fileName.endsWith ".lean" then
          let fullPath : System.FilePath := ⟨dirPath⟩ / entry.fileName
          let content ← IO.FS.readFile fullPath
          let lines := content.splitOn "\n"
          if lines.length > 900 then
            IO.println s!"ERROR: {fullPath} has {lines.length} lines (max 900)"
            violation := true
      return violation
    else
      return false

  let v1 ← checkFiles "src"
  if v1 then exitCode := 1

  let v2 ← checkFiles "test"
  if v2 then exitCode := 1

  IO.println "\n========================"
  if exitCode == 0 then
    IO.println "PASS: All lint checks passed!"
  else
    IO.println "FAIL: Some lint checks failed"

  return exitCode.toUInt32

-- Documentation builder script
script docs do
  IO.println "Building documentation..."

  -- Create docbuild directory if it doesn't exist
  let docbuildPath : System.FilePath := ⟨"docbuild"⟩
  if !(← docbuildPath.pathExists) then
    IO.FS.createDir docbuildPath

  -- Create lakefile.lean for docbuild
  let lakefilePath := docbuildPath / "lakefile.lean"
  let lakefileContent := "import Lake
open Lake DSL

package «docbuild»

require «MyProject» from \"..\"

require «doc-gen4» from git
  \"https://github.com/leanprover/doc-gen4\" @ \"31cc380\"
"
  IO.FS.writeFile lakefilePath lakefileContent

  -- Copy lean-toolchain
  let toolchainSrc : System.FilePath := ⟨"lean-toolchain"⟩
  let toolchainDst := docbuildPath / "lean-toolchain"
  if ← toolchainSrc.pathExists then
    let content ← IO.FS.readFile toolchainSrc
    IO.FS.writeFile toolchainDst content

  -- Run lake update in docbuild
  IO.println "Updating dependencies..."
  let updateProc ← IO.Process.spawn {
    cmd := "lake"
    args := #["update"]
    cwd := docbuildPath
    env := #[("MATHLIB_NO_CACHE_ON_UPDATE", "1")]
  }
  let updateExitCode ← updateProc.wait
  if updateExitCode ≠ 0 then
    IO.println "Error: Failed to update dependencies"
    return 1

  -- Build documentation
  IO.println "Generating documentation..."
  let buildProc ← IO.Process.spawn {
    cmd := "lake"
    args := #["build", "MyProject:docs"]
    cwd := docbuildPath
  }
  let buildExitCode ← buildProc.wait
  if buildExitCode ≠ 0 then
    IO.println "Error: Failed to build documentation"
    return 1

  IO.println "Documentation generated successfully!"
  IO.println "View docs at: docbuild/.lake/build/doc/"
  IO.println "To serve locally, run:"
  IO.println "  cd docbuild/.lake/build/doc && python3 -m http.server"
  return 0
