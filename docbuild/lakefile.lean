import Lake
open Lake DSL

package «docbuild»

require «MyProject» from ".."

require «doc-gen4» from git
  "https://github.com/leanprover/doc-gen4" @ "31cc380"
