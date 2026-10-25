import DegreeNecessity.Result
import Lean.Util.CollectAxioms
import Lean.PrivateName

/-!
Transitive axiom audit of the complete counterexample and all its local theorems.
Only propositional extensionality, classical choice and quotient soundness are allowed.
-/
#check SPR.DegreeNecessity.counterexample
#print axioms SPR.DegreeNecessity.counterexample
#print axioms SPR.DegreeNecessity.no_nonzero_weak

run_cmd do
  let env ← Lean.getEnv
  let allowed : List Lean.Name := [`propext, `Classical.choice, `Quot.sound]
  let mut checked := 0
  for (name, info) in env.constants.toList do
    let userName := Lean.privateToUserName name
    if (`SPR).isPrefixOf userName && info.isTheorem then
      for axiomName in (← Lean.collectAxioms name) do
        unless allowed.contains axiomName do
          throwError "Unexpected axiom {axiomName} in {name}"
      checked := checked + 1
  if checked < 35 then
    throwError "Incomplete counterexample import: {checked} theorems"
  Lean.logInfo m!"Axiom audit passed: {checked} SPR theorems; only propext, Classical.choice, Quot.sound"
