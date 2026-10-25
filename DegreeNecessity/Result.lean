import DegreeNecessity.Witness
import DegreeNecessity.Exclusion

/-!
# The explicit degree-necessity counterexample

This module assembles full independent widths, robust Hurwitz stability, the
fixed exact-degree-six numerator, and exclusion of every nonzero polynomial
of degree at most five even under weak frequency positivity.
-/
namespace SPR.DegreeNecessity
noncomputable section
open Polynomial N6

/-- Complete statement for the concrete box and numerator defined in `Basic`.
`CommonWeak` in `Exclusion` quantifies over every box member and every real frequency. -/
def Statement : Prop :=
  (lower.a1 < upper.a1 ∧ lower.a2 < upper.a2 ∧ lower.a3 < upper.a3 ∧
    lower.a4 < upper.a4 ∧ lower.a5 < upper.a5 ∧ lower.a6 < upper.a6) ∧
  box.RobustlyHurwitz ∧
  (numeratorPoly witness).natDegree = 6 ∧
  (∀ a : Poly6, box.Contains a → FrequencySPR a.toPoly (numeratorPoly witness)) ∧
  ¬ ∃ p : ℝ[X], p ≠ 0 ∧ p.natDegree ≤ 5 ∧ CommonWeak p

/-- The full sextic example, with no stability or certificate premise. -/
theorem counterexample : Statement :=
  ⟨full_width, robustly_hurwitz, witness_degree, fun _ ha => witness_spr ha,
    no_nonzero_weak⟩

end
end SPR.DegreeNecessity
