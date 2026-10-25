import SPR.Segment.FrequencyIdentities
import SPR.Segment.HalfPlane
import SPR.Segment.RationalDecay
import SPR.Segment.Boundedness

/-!
# Strict interior positivity for weak positive-real polynomial quotients

For a Hurwitz denominator and a nonzero numerator of strictly lower degree,
imaginary-axis nonnegativity implies strict positivity on the open right
half-plane. Analyticity, boundedness and nontriviality are proved here from
the polynomials; they are not extra synthesis hypotheses.
-/

namespace SPR.Segment

open Polynomial Complex Set Filter Bornology
open scoped Topology

noncomputable section

/-- A nonzero real polynomial is nonzero at some positive real argument. -/
theorem exists_positive_nonroot {c : ℝ[X]} (hc : c ≠ 0) :
    ∃ x : ℝ, 0 < x ∧ c.eval x ≠ 0 := by
  by_contra! h
  apply hc
  exact c.eq_zero_of_infinite_isRoot ((Set.Ioi_infinite (0 : ℝ)).mono
    (fun x hx => h x hx))

/-- Strictly proper nonzero weak positive-real quotients are strict inside the half-plane. -/
theorem weak_ratio_strict_interior {p c : ℝ[X]} (hp : IsHurwitz p) (hc : c ≠ 0)
    (hdeg : c.natDegree < p.natDegree)
    (hweak : ∀ ω : ℝ, 0 ≤ (value c (I * (ω : ℂ)) / value p (I * (ω : ℂ))).re)
    {z : ℂ} (hz : 0 < z.re) : 0 < (value c z / value p z).re := by
  let F : ℂ → ℂ := fun w => value c w / value p w
  have hp0 : p ≠ 0 := by
    intro he
    have hh := hp 0 (by simp [he, IsRoot])
    simp at hh
  have hn (w : ℂ) (hw : 0 ≤ w.re) : value p w ≠ 0 := value_ne_zero hp hw
  have hclosed : IsClosed {w : ℂ | 0 ≤ w.re} := isClosed_le continuous_const continuous_re
  have hcont : ContinuousOn F {w : ℂ | 0 ≤ w.re} :=
    c.continuous_aeval.continuousOn.div p.continuous_aeval.continuousOn hn
  have hd : DiffContOnCl ℂ F Analysis.rightHalfPlane := by
    constructor
    · intro w hw
      exact c.differentiableWithinAt_aeval.div p.differentiableWithinAt_aeval (hn w hw.le)
    · simpa only [Analysis.rightHalfPlane, closure_setOf_lt_re] using hcont
  have hlim : Tendsto F (cobounded ℂ) (𝓝 0) := by
    have hm : p.map (algebraMap ℝ ℂ) ≠ 0 := map_ne_zero hp0
    have hdm : (c.map (algebraMap ℝ ℂ)).natDegree <
        (p.map (algebraMap ℝ ℂ)).natDegree := by simpa only [natDegree_map] using hdeg
    have hh := Analysis.quotient_tendsto_zero
      (p := c.map (algebraMap ℝ ℂ)) (q := p.map (algebraMap ℝ ℂ)) hm hdm
    simpa only [F, value, eval_map] using hh
  have hb : ∃ M : ℝ, ∀ w : ℂ, 0 ≤ w.re → ‖F w‖ ≤ M :=
    Analysis.bounded_on_closed_of_tendsto hclosed hcont hlim
  have hboundary (ω : ℝ) : 0 ≤ (F ((ω : ℂ) * I)).re := by
    simpa only [F, mul_comm (ω : ℂ) I] using hweak ω
  have hnot : ∃ w : ℂ, 0 < w.re ∧ (F w).re ≠ 0 := by
    obtain ⟨x, hx, hcx⟩ := exists_positive_nonroot hc
    refine ⟨x, hx, ?_⟩
    have hcv : value c (x : ℂ) = Complex.ofReal (c.eval x) :=
      Polynomial.aeval_ofReal (K := ℂ) c x
    have hpv : value p (x : ℂ) = Complex.ofReal (p.eval x) :=
      Polynomial.aeval_ofReal (K := ℂ) p x
    have hpx : p.eval x ≠ 0 := by
      intro he
      apply hn x hx.le
      rw [hpv, he]
      simp
    change (value c (x : ℂ) / value p (x : ℂ)).re ≠ 0
    rw [hcv, hpv, ← ofReal_div, ofReal_re]
    exact div_ne_zero hcx hpx
  exact Analysis.real_strict hd hb hboundary hnot hz

end
end SPR.Segment
