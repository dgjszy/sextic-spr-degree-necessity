import SPR.N6.Preliminaries.HurwitzPhase

/-!
# Six-degree parity interlacing from Hurwitz stability

Five phase levels yield three even roots and two odd roots. Exact polynomial
factorizations establish completeness and simplicity, not just existence of
sampled sign changes.
-/
namespace SPR.N6
noncomputable section
open Polynomial Filter Set
open scoped Topology

/-- Every phase level strictly between zero and the sextic limiting phase is attained. -/
theorem rootPhase_hits {a : Poly6} (ha : IsHurwitz a.toPoly) {y : ℝ}
    (hy0 : 0 < y) (hy : y < 6 * Real.pi / 2) :
    ∃ ω : ℝ, 0 < ω ∧ rootPhase a ω = y := by
  have he : ∀ᶠ ω : ℝ in atTop, y < rootPhase a ω :=
    (rootPhase_tendsto ha).eventually (lt_mem_nhds hy)
  obtain ⟨w, hw0, hwy⟩ := ((eventually_gt_atTop (0 : ℝ)).and he).exists
  have hymem : y ∈ Icc (rootPhase a 0) (rootPhase a w) := by
    rw [rootPhase_zero]
    exact ⟨hy0.le, hwy.le⟩
  obtain ⟨ω, hω, hphase⟩ := intermediate_value_Icc hw0.le
    (rootPhase_continuous ha).continuousOn hymem
  have hω0 : 0 < ω := lt_of_le_of_ne hω.1 (by
    intro heq
    have h := hphase
    rw [← heq, rootPhase_zero] at h
    linarith)
  exact ⟨ω, hω0, hphase⟩

/-- All five positive parity roots in their strict alternating order. -/
theorem hurwitz_interlacing_roots {a : Poly6} (ha : IsHurwitz a.toPoly) :
    ∃ e₁ o₁ e₂ o₂ e₃ : ℝ,
      0 < e₁ ∧ e₁ < o₁ ∧ o₁ < e₂ ∧ e₂ < o₂ ∧ o₂ < e₃ ∧
      evenPart a e₁ = 0 ∧ oddPart a o₁ = 0 ∧ evenPart a e₂ = 0 ∧
      oddPart a o₂ = 0 ∧ evenPart a e₃ = 0 := by
  have hp := Real.pi_pos
  obtain ⟨v₁, hv₁, h₁⟩ := rootPhase_hits ha (y := Real.pi / 2) (by linarith) (by linarith)
  obtain ⟨v₂, hv₂, h₂⟩ := rootPhase_hits ha (y := Real.pi) hp (by linarith)
  obtain ⟨v₃, hv₃, h₃⟩ := rootPhase_hits ha (y := Real.pi / 2 + Real.pi)
    (by linarith) (by linarith)
  obtain ⟨v₄, hv₄, h₄⟩ := rootPhase_hits ha (y := Real.pi + Real.pi)
    (by linarith) (by linarith)
  obtain ⟨v₅, hv₅, h₅⟩ := rootPhase_hits ha (y := Real.pi / 2 + (Real.pi + Real.pi))
    (by linarith) (by linarith)
  have hv12 : v₁ < v₂ := (rootPhase_strictMono ha).lt_iff_lt.mp (by rw [h₁, h₂]; linarith)
  have hv23 : v₂ < v₃ := (rootPhase_strictMono ha).lt_iff_lt.mp (by rw [h₂, h₃]; linarith)
  have hv34 : v₃ < v₄ := (rootPhase_strictMono ha).lt_iff_lt.mp (by rw [h₃, h₄]; linarith)
  have hv45 : v₄ < v₅ := (rootPhase_strictMono ha).lt_iff_lt.mp (by rw [h₄, h₅]; linarith)
  refine ⟨v₁ ^ 2, v₂ ^ 2, v₃ ^ 2, v₄ ^ 2, v₅ ^ 2, sq_pos_of_pos hv₁,
    (sq_lt_sq₀ hv₁.le hv₂.le).mpr hv12, (sq_lt_sq₀ hv₂.le hv₃.le).mpr hv23,
    (sq_lt_sq₀ hv₃.le hv₄.le).mpr hv34, (sq_lt_sq₀ hv₄.le hv₅.le).mpr hv45,
    ?_, ?_, ?_, ?_, ?_⟩
  · simpa [h₁] using frequencyValue_phase_re ha v₁
  · have h := frequencyValue_phase_im ha v₂
    simp only [h₂, Real.sin_pi, mul_zero] at h
    exact (mul_eq_zero.mp h).resolve_left (ne_of_gt hv₂)
  · simpa [h₃, Real.cos_add] using frequencyValue_phase_re ha v₃
  · have h := frequencyValue_phase_im ha v₄
    simp only [h₄, Real.sin_add, Real.sin_pi, Real.cos_pi, zero_mul, mul_zero, add_zero] at h
    exact (mul_eq_zero.mp h).resolve_left (ne_of_gt hv₄)
  · simpa [h₅, Real.cos_add, Real.sin_add] using frequencyValue_phase_re ha v₅

private theorem linear_coprime {r s : ℝ} (hrs : r ≠ s) :
    IsCoprime (X - C r : ℝ[X]) (X - C s) :=
  isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.mpr hrs).isUnit

/-- A quadratic is completely determined by two distinct roots and its leading coefficient. -/
theorem quadratic_factor_of_two_roots {p : ℝ[X]} (hdeg : p.natDegree ≤ 2)
    {r s : ℝ} (hrs : r ≠ s) (hr : p.eval r = 0) (hs : p.eval s = 0) :
    p = C (p.coeff 2) * ((X - C r) * (X - C s)) := by
  have hmonic := (monic_X_sub_C r).mul (monic_X_sub_C s)
  have hdvd := (linear_coprime hrs).mul_dvd
    (dvd_iff_isRoot.mpr hr) (dvd_iff_isRoot.mpr hs)
  have hbase : ((X - C r) * (X - C s) : ℝ[X]).natDegree = 2 := by
    rw [(monic_X_sub_C r).natDegree_mul (monic_X_sub_C s)]
    simp
  have hform := eq_leadingCoeff_mul_of_monic_of_dvd_of_natDegree_le
    hmonic hdvd (by rwa [hbase])
  have hc : p.coeff 2 = p.leadingCoeff := by
    conv_lhs => rw [hform]
    rw [coeff_C_mul, ← hbase, coeff_natDegree, hmonic.leadingCoeff, mul_one]
  rwa [hc]

/-- Three distinct roots exhaust a cubic. -/
theorem cubic_factor_of_three_roots {p : ℝ[X]} (hdeg : p.natDegree ≤ 3)
    {r s t : ℝ} (hrs : r ≠ s) (hrt : r ≠ t) (hst : s ≠ t)
    (hr : p.eval r = 0) (hs : p.eval s = 0) (ht : p.eval t = 0) :
    p = C (p.coeff 3) * (((X - C r) * (X - C s)) * (X - C t)) := by
  have hmonic := ((monic_X_sub_C r).mul (monic_X_sub_C s)).mul (monic_X_sub_C t)
  have hpair := (linear_coprime hrs).mul_dvd
    (dvd_iff_isRoot.mpr hr) (dvd_iff_isRoot.mpr hs)
  have hdvd := ((linear_coprime hrt).mul_left (linear_coprime hst)).mul_dvd
    hpair (dvd_iff_isRoot.mpr ht)
  have hbase : (((X - C r) * (X - C s)) * (X - C t) : ℝ[X]).natDegree = 3 := by
    compute_degree!
  have hform := eq_leadingCoeff_mul_of_monic_of_dvd_of_natDegree_le
    hmonic hdvd (by rwa [hbase])
  have hc : p.coeff 3 = p.leadingCoeff := by
    conv_lhs => rw [hform]
    rw [coeff_C_mul, ← hbase, coeff_natDegree, hmonic.leadingCoeff, mul_one]
  rwa [hc]

/-- The complete ordered root data extracted from one actual Hurwitz sextic. -/
structure DenominatorInterlacing (a : Poly6) where
  e₁ : ℝ
  o₁ : ℝ
  e₂ : ℝ
  o₂ : ℝ
  e₃ : ℝ
  e₁_pos : 0 < e₁
  e₁_lt_o₁ : e₁ < o₁
  o₁_lt_e₂ : o₁ < e₂
  e₂_lt_o₂ : e₂ < o₂
  o₂_lt_e₃ : o₂ < e₃
  even_factor : evenPoly a = -(((X - C e₁) * (X - C e₂)) * (X - C e₃))
  odd_factor : oddPoly a = C a.a1 * ((X - C o₁) * (X - C o₂))

/-- Strict Hurwitz stability supplies all root data, including exact factorizations. -/
theorem denominator_interlacing {a : Poly6} (ha : IsHurwitz a.toPoly) :
    Nonempty (DenominatorInterlacing a) := by
  obtain ⟨e₁, o₁, e₂, o₂, e₃, he, heo, hoe, heo', hoe', hE₁, hO₁, hE₂, hO₂, hE₃⟩ :=
    hurwitz_interlacing_roots ha
  have hedeg : (evenPoly a).natDegree ≤ 3 := by unfold evenPoly; compute_degree!
  have hodeg : (oddPoly a).natDegree ≤ 2 := by unfold oddPoly; compute_degree!
  have hEe (t : ℝ) : (evenPoly a).eval t = evenPart a t := by simp [evenPoly, evenPart]
  have hOo (t : ℝ) : (oddPoly a).eval t = oddPart a t := by simp [oddPoly, oddPart]
  have h12 := heo.trans hoe
  have h23 := heo'.trans hoe'
  have hEf := cubic_factor_of_three_roots hedeg (ne_of_lt h12)
    (ne_of_lt (h12.trans h23)) (ne_of_lt h23)
    (by rwa [hEe]) (by rwa [hEe]) (by rwa [hEe])
  have hOf := quadratic_factor_of_two_roots hodeg (ne_of_lt (hoe.trans heo'))
    (by rwa [hOo]) (by rwa [hOo])
  refine ⟨⟨e₁, o₁, e₂, o₂, e₃, he, heo, hoe, heo', hoe', ?_, ?_⟩⟩
  · simpa [evenPoly, coeff_sub, coeff_add, coeff_C_mul_X_pow] using hEf
  · simpa [oddPoly, coeff_sub, coeff_add, coeff_C_mul_X_pow] using hOf

namespace DenominatorInterlacing

theorem even_value {a : Poly6} (d : DenominatorInterlacing a) (t : ℝ) :
    evenPart a t = -(t - d.e₁) * (t - d.e₂) * (t - d.e₃) := by
  have h := congrArg (Polynomial.eval t) d.even_factor
  calc
    evenPart a t = -((t - d.e₁) * (t - d.e₂) * (t - d.e₃)) := by
      simpa [evenPoly, evenPart] using h
    _ = _ := by ring

theorem odd_value {a : Poly6} (d : DenominatorInterlacing a) (t : ℝ) :
    oddPart a t = a.a1 * (t - d.o₁) * (t - d.o₂) := by
  have h := congrArg (Polynomial.eval t) d.odd_factor
  simpa [oddPoly, oddPart, mul_assoc] using h

end DenominatorInterlacing
end
end SPR.N6
