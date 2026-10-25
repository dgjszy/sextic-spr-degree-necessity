import Lake
open Lake DSL

run_cmd do
  unless Lean.versionString == "4.30.0" do
    throwError "This proof package requires Lean 4.30.0"

/-!
Minimal standalone package for the explicit sextic degree-necessity example.
Use the pinned compiler: elan run leanprover/lean4:v4.30.0 lake build
The default target checks the complete theorem and its transitive axioms.
-/
package sextic_spr_degree_necessity where
  moreLeanArgs := #["-DrelaxedAutoImplicit=false", "-DmaxSynthPendingDepth=3"]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @
  "c5ea00351c28e24afc9f0f84379aa41082b1188f"

@[default_target]
lean_lib Counterexample where
  roots := #[`DegreeNecessity.Result, `Audit]
  globs := #[.one `Audit, .submodules `DegreeNecessity, .submodules `SPR]
