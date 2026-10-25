import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Uniform decay of strictly proper polynomial quotients

Reversal rewrites the quotient in terms of `1/z`. This proves decay at complex
infinity in all directions, which is stronger than decay on the imaginary axis.
-/

namespace SPR.Segment.Analysis

open Polynomial Filter Bornology
open scoped Topology

noncomputable section

theorem eval_reverse_identity (p : ℂ[X]) {z : ℂ} (hz : z ≠ 0) :
    p.reverse.eval z⁻¹ * z ^ p.natDegree = p.eval z := by
  letI : Invertible z := invertibleOfNonzero hz
  simpa using eval₂_reverse_mul_pow (RingHom.id ℂ) z p

/-- Reversal exposes the degree difference as a positive power of `1/z`. -/
theorem quotient_reverse (p q : ℂ[X]) (hdeg : p.natDegree ≤ q.natDegree)
    {z : ℂ} (hz : z ≠ 0) :
    p.eval z / q.eval z =
      z⁻¹ ^ (q.natDegree - p.natDegree) * (p.reverse.eval z⁻¹ / q.reverse.eval z⁻¹) := by
  rw [← eval_reverse_identity p hz, ← eval_reverse_identity q hz]
  have hsum : q.natDegree = p.natDegree + (q.natDegree - p.natDegree) := by omega
  have hpow : z ^ q.natDegree = z ^ p.natDegree * z ^ (q.natDegree - p.natDegree) := by
    calc
      _ = z ^ (p.natDegree + (q.natDegree - p.natDegree)) := congrArg (z ^ ·) hsum
      _ = _ := pow_add _ _ _
  rw [hpow, inv_pow]
  by_cases hq : q.reverse.eval z⁻¹ = 0
  · simp [hq]
  · field_simp

/-- Strictly proper quotients tend uniformly to zero at complex infinity. -/
theorem quotient_tendsto_zero {p q : ℂ[X]} (hq : q ≠ 0)
    (hdeg : p.natDegree < q.natDegree) :
    Tendsto (fun z : ℂ => p.eval z / q.eval z) (cobounded ℂ) (𝓝 0) := by
  have hi : Tendsto (fun z : ℂ => z⁻¹) (cobounded ℂ) (𝓝 0) := tendsto_inv₀_cobounded
  have hp := p.reverse.continuous.tendsto 0 |>.comp hi
  have hq' := q.reverse.continuous.tendsto 0 |>.comp hi
  have hq0 : q.reverse.eval 0 ≠ 0 := by
    rw [← coeff_zero_eq_eval_zero, coeff_zero_reverse]
    exact leadingCoeff_ne_zero.mpr hq
  have hpow : Tendsto (fun z : ℂ => z⁻¹ ^ (q.natDegree - p.natDegree))
      (cobounded ℂ) (𝓝 0) := by
    have hd : q.natDegree - p.natDegree ≠ 0 := by omega
    simpa [zero_pow hd] using hi.pow (q.natDegree - p.natDegree)
  have hlim := hpow.mul (hp.div hq' hq0)
  simp only [zero_mul] at hlim
  apply hlim.congr'
  filter_upwards [eventually_ne_cobounded (0 : ℂ)] with z hz
  exact (quotient_reverse p q hdeg.le hz).symm

end
end SPR.Segment.Analysis
