import Mathlib.Analysis.Complex.PhragmenLindelof
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Convex.Topology
import Mathlib.Tactic.Linarith

/-!
# From boundary nonnegativity to strict interior positivity

Apply the half-plane maximum principle to `exp (-F)`. Boundedness of `F`
provides the growth bound. If the real part vanishes at an interior point,
the strong maximum principle forces it to vanish throughout the half-plane.
For rational functions the analytic, boundedness and nontriviality hypotheses
must still be derived from the actual numerator and denominator polynomials.
-/

namespace SPR.Segment.Analysis

open Complex Set Filter Asymptotics Bornology

noncomputable section

/-- The open right half-plane. -/
def rightHalfPlane : Set ℂ := {z | 0 < z.re}

theorem rightHalfPlane_open : IsOpen rightHalfPlane :=
  isOpen_lt continuous_const continuous_re

theorem rightHalfPlane_convex : Convex ℝ rightHalfPlane :=
  (convex_Ioi (0 : ℝ)).linear_preimage Complex.reLm

/-- A bounded holomorphic function with nonnegative real boundary values
has nonnegative real part on the closed right half-plane. -/
theorem real_nonneg {F : ℂ → ℂ}
    (hd : DiffContOnCl ℂ F rightHalfPlane)
    (hb : ∃ M : ℝ, ∀ z : ℂ, 0 ≤ z.re → ‖F z‖ ≤ M)
    (hboundary : ∀ ω : ℝ, 0 ≤ (F ((ω : ℂ) * I)).re)
    {z : ℂ} (hz : 0 ≤ z.re) : 0 ≤ (F z).re := by
  obtain ⟨M, hM⟩ := hb
  let G : ℂ → ℂ := fun w => Complex.exp (-F w)
  have hGd : DiffContOnCl ℂ G {w : ℂ | 0 < w.re} :=
    ⟨hd.differentiableOn.neg.cexp, continuous_exp.comp_continuousOn hd.continuousOn.neg⟩
  have hGb (w : ℂ) (hw : 0 ≤ w.re) : ‖G w‖ ≤ Real.exp M := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    simp only [Complex.neg_re]
    exact ((neg_le_abs (F w).re).trans (Complex.abs_re_le_norm (F w))).trans (hM w hw)
  have hgrowth : ∃ c < (2 : ℝ), ∃ B,
      G =O[cobounded ℂ ⊓ 𝓟 {w : ℂ | 0 < w.re}]
        (fun w => Real.exp (B * ‖w‖ ^ c)) := by
    refine ⟨0, by norm_num, 0, IsBigO.of_bound (Real.exp M) ?_⟩
    apply eventually_inf_principal.mpr
    exact Eventually.of_forall (fun w hw => by simpa using hGb w hw.le)
  have hreal : IsBoundedUnder (· ≤ ·) atTop (fun x : ℝ => ‖G x‖) :=
    isBoundedUnder_of_eventually_le (by
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
      exact hGb x hx)
  have haxis (ω : ℝ) : ‖G ((ω : ℂ) * I)‖ ≤ 1 := by
    rw [Complex.norm_exp]
    apply Real.exp_le_one_iff.mpr
    simpa using neg_nonpos.mpr (hboundary ω)
  have hnorm : ‖G z‖ ≤ 1 :=
    PhragmenLindelof.right_half_plane_of_bounded_on_real
      hGd hgrowth hreal haxis hz
  rw [Complex.norm_exp, Real.exp_le_one_iff] at hnorm
  simpa using hnorm

/-- The real part is either everywhere zero or strictly positive at every interior point. -/
theorem real_strict {F : ℂ → ℂ}
    (hd : DiffContOnCl ℂ F rightHalfPlane)
    (hb : ∃ M : ℝ, ∀ z : ℂ, 0 ≤ z.re → ‖F z‖ ≤ M)
    (hboundary : ∀ ω : ℝ, 0 ≤ (F ((ω : ℂ) * I)).re)
    (hnot : ∃ w : ℂ, 0 < w.re ∧ (F w).re ≠ 0)
    {z : ℂ} (hz : 0 < z.re) : 0 < (F z).re := by
  have hn (w : ℂ) (hw : 0 ≤ w.re) := real_nonneg hd hb hboundary hw
  apply lt_of_le_of_ne (hn z hz.le)
  intro hzero
  let G : ℂ → ℂ := fun w => Complex.exp (-F w)
  have hGd : DifferentiableOn ℂ G rightHalfPlane := hd.differentiableOn.neg.cexp
  have hGz : ‖G z‖ = 1 := by simp [G, Complex.norm_exp, hzero.symm]
  have hmax : IsMaxOn (norm ∘ G) rightHalfPlane z := by
    intro w hw
    change ‖G w‖ ≤ ‖G z‖
    rw [hGz, Complex.norm_exp]
    exact Real.exp_le_one_iff.mpr (by simpa using neg_nonpos.mpr (hn w hw.le))
  have heq := Complex.norm_eqOn_of_isPreconnected_of_isMaxOn
    rightHalfPlane_convex.isPreconnected rightHalfPlane_open hGd hz hmax
  obtain ⟨w, hw, hFw⟩ := hnot
  have hnorm : ‖G w‖ = 1 := (heq hw).trans hGz
  rw [Complex.norm_exp, ← Real.exp_zero, Real.exp_eq_exp] at hnorm
  exact hFw (by simpa using hnorm)

end
end SPR.Segment.Analysis
