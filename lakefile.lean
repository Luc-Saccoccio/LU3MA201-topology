import Lake
open Lake DSL

package «topology» where
  -- add package configuration options here

lean_lib «Topology» where
  -- add library configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4"
