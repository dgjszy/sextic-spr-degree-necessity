import DegreeNecessity.RootBands

/-!
# Hurwitz stability from strict sextic interlacing

Positive residues express the odd/even quotient as a sum of resonators.
Their real parts are nonnegative on the right half-plane. Strict interlacing
also excludes imaginary-axis zeros.
-/
namespace SPR.DegreeNecessity
noncomputable section
open Polynomial N6 Complex

/-- A resonator has nonnegative real part in the closed right half-plane. -/
theorem resonator_nonneg {z : ℂ} {e : ℝ} (hz : 0 ≤ z.re) (he : 0 ≤ e) :
    0 ≤ (z / (z^2 + (e : ℂ))).re := by
  rw [Complex.div_re, ← add_div]
  apply div_nonneg _ (Complex.normSq_nonneg _)
  have h := mul_nonneg hz (add_nonneg (Complex.normSq_nonneg z) he)
  simp only [pow_two, mul_re, mul_im, add_re, add_im, ofReal_re, ofReal_im,
    add_zero, normSq_apply] at *
  nlinarith only [h]

/-- Positive frequency factors cannot vanish in the open right half-plane. -/
theorem quadratic_ne_zero {z : ℂ} {e : ℝ} (hz : 0 < z.re) (he : 0 < e) :
    z^2 + (e : ℂ) ≠ 0 := by
  intro h
  have hr := congrArg Complex.re h
  have hi := congrArg Complex.im h
  simp only [pow_two, mul_re, mul_im, add_re, add_im, ofReal_re, ofReal_im,
    zero_re, zero_im, add_zero] at hr hi
  have hy : z.im = 0 := by nlinarith
  rw [hy] at hr
  nlinarith [sq_nonneg z.re]

/-- Interlacing gives the factorization of the original sextic at any complex point. -/
theorem interlacing_value {a : Poly6} (d : DenominatorInterlacing a) (z : ℂ) :
    a.toPoly.eval₂ (algebraMap ℝ ℂ) z =
      (z^2+(d.e₁:ℂ))*(z^2+(d.e₂:ℂ))*(z^2+(d.e₃:ℂ)) +
      z*(a.a1:ℂ)*(z^2+(d.o₁:ℂ))*(z^2+(d.o₂:ℂ)) := by
  have h : a.toPoly = (evenPoly a).comp (-X^2) + X*(oddPoly a).comp (-X^2) := by
    simp [Poly6.toPoly, evenPoly, oddPoly]
    ring
  rw [h, d.even_factor, d.odd_factor]
  simp
  ring

/-- The three residues of a strictly interlacing quadratic/cubic pair are positive. -/
theorem residues_pos {a : Poly6} (d : DenominatorInterlacing a) (ha : 0 < a.a1) :
    0 < a.a1*(d.e₁-d.o₁)*(d.e₁-d.o₂)/((d.e₁-d.e₂)*(d.e₁-d.e₃)) ∧
    0 < a.a1*(d.e₂-d.o₁)*(d.e₂-d.o₂)/((d.e₂-d.e₁)*(d.e₂-d.e₃)) ∧
    0 < a.a1*(d.e₃-d.o₁)*(d.e₃-d.o₂)/((d.e₃-d.e₁)*(d.e₃-d.e₂)) := by
  have h12 := d.e₁_lt_o₁.trans d.o₁_lt_e₂
  have h23 := d.e₂_lt_o₂.trans d.o₂_lt_e₃
  have h13 := h12.trans h23
  constructor
  · exact div_pos
      (mul_pos_of_neg_of_neg (mul_neg_of_pos_of_neg ha (sub_neg.mpr d.e₁_lt_o₁))
        (sub_neg.mpr (h12.trans d.e₂_lt_o₂)))
      (mul_pos_of_neg_of_neg (sub_neg.mpr h12) (sub_neg.mpr h13))
  constructor
  · exact div_pos_of_neg_of_neg
      (mul_neg_of_pos_of_neg (mul_pos ha (sub_pos.mpr d.o₁_lt_e₂))
        (sub_neg.mpr d.e₂_lt_o₂))
      (mul_neg_of_pos_of_neg (sub_pos.mpr h12) (sub_neg.mpr h23))
  · exact div_pos
      (mul_pos (mul_pos ha (sub_pos.mpr (d.o₁_lt_e₂.trans h23)))
        (sub_pos.mpr d.o₂_lt_e₃))
      (mul_pos (sub_pos.mpr h13) (sub_pos.mpr h23))

/-- Three-node partial fractions, as a polynomial identity after clearing denominators. -/
theorem residue_identity {x y z u v c : ℂ} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (s : ℂ) :
    c*(s+u)*(s+v) =
      (c*(x-u)*(x-v)/((x-y)*(x-z)))*(s+y)*(s+z) +
      (c*(y-u)*(y-v)/((y-x)*(y-z)))*(s+x)*(s+z) +
      (c*(z-u)*(z-v)/((z-x)*(z-y)))*(s+x)*(s+y) := by
  field_simp [sub_ne_zero.mpr hxy, sub_ne_zero.mpr hxz, sub_ne_zero.mpr hyz,
    sub_ne_zero.mpr hxy.symm, sub_ne_zero.mpr hxz.symm, sub_ne_zero.mpr hyz.symm]
  <;> ring

/-- Strict sextic interlacing is sufficient for Hurwitz stability. -/
theorem hurwitz_of_interlacing {a : Poly6} (d : DenominatorInterlacing a)
    (ha : 0 < a.a1) : SPR.IsHurwitz a.toPoly := by
  intro z hz
  change (a.toPoly.map (algebraMap ℝ ℂ)).eval z = 0 at hz
  rw [eval_map] at hz
  by_contra hn
  have hre : 0 ≤ z.re := le_of_not_gt hn
  have h12 := d.e₁_lt_o₁.trans d.o₁_lt_e₂
  have h23 := d.e₂_lt_o₂.trans d.o₂_lt_e₃
  have h13 := h12.trans h23
  have he₂ := d.e₁_pos.trans h12
  have he₃ := d.e₁_pos.trans h13
  by_cases hzero : z.re = 0
  · have hzform : z = I*(z.im:ℂ) := by apply Complex.ext <;> simp [hzero]
    have hf : frequencyValue a z.im = 0 := by
      unfold frequencyValue
      rw [eval_map, ← hzform]
      exact hz
    have hr := congrArg Complex.re hf
    have hi := congrArg Complex.im hf
    rw [frequencyValue_re, d.even_value] at hr
    rw [frequencyValue_im, d.odd_value] at hi
    simp only [zero_re, zero_im] at hr hi
    have ht : z.im^2 = d.e₁ ∨ z.im^2 = d.e₂ ∨ z.im^2 = d.e₃ := by
      rcases mul_eq_zero.mp hr with h | h
      · rcases mul_eq_zero.mp h with h | h
        · exact Or.inl (by linarith)
        · exact Or.inr (Or.inl (sub_eq_zero.mp h))
      · exact Or.inr (Or.inr (sub_eq_zero.mp h))
    rcases ht with ht | ht | ht
    all_goals
      have him : z.im ≠ 0 := by intro hh; rw [hh] at ht; norm_num at ht; linarith [d.e₁_pos]
      have ho : a.a1*(z.im^2-d.o₁)*(z.im^2-d.o₂) = 0 :=
        (mul_eq_zero.mp hi).resolve_left him
      rcases mul_eq_zero.mp ho with h | h
      · rcases mul_eq_zero.mp h with h | h
        · exact ha.ne' h
        · rw [ht] at h; linarith [d.e₁_lt_o₁, d.o₁_lt_e₂, d.e₂_lt_o₂, d.o₂_lt_e₃]
      · rw [ht] at h; linarith [d.e₁_lt_o₁, d.o₁_lt_e₂, d.e₂_lt_o₂, d.o₂_lt_e₃]
  · have hp : 0 < z.re := lt_of_le_of_ne hre (Ne.symm hzero)
    let g₁ := a.a1*(d.e₁-d.o₁)*(d.e₁-d.o₂)/((d.e₁-d.e₂)*(d.e₁-d.e₃))
    let g₂ := a.a1*(d.e₂-d.o₁)*(d.e₂-d.o₂)/((d.e₂-d.e₁)*(d.e₂-d.e₃))
    let g₃ := a.a1*(d.e₃-d.o₁)*(d.e₃-d.o₂)/((d.e₃-d.e₁)*(d.e₃-d.e₂))
    obtain ⟨hg₁,hg₂,hg₃⟩ := residues_pos d ha
    have hn₁ := quadratic_ne_zero hp d.e₁_pos
    have hn₂ := quadratic_ne_zero hp he₂
    have hn₃ := quadratic_ne_zero hp he₃
    have hid := residue_identity (c := (a.a1:ℂ)) (u := (d.o₁:ℂ)) (v := (d.o₂:ℂ))
      (show (d.e₁:ℂ) ≠ (d.e₂:ℂ) by exact_mod_cast h12.ne)
      (show (d.e₁:ℂ) ≠ (d.e₃:ℂ) by exact_mod_cast h13.ne)
      (show (d.e₂:ℂ) ≠ (d.e₃:ℂ) by exact_mod_cast h23.ne) (z^2)
    have heq : (1:ℂ) + (g₁:ℂ)*(z/(z^2+(d.e₁:ℂ))) +
        (g₂:ℂ)*(z/(z^2+(d.e₂:ℂ))) + (g₃:ℂ)*(z/(z^2+(d.e₃:ℂ))) = 0 := by
      rw [interlacing_value d] at hz
      have hid' : (a.a1:ℂ)*(z^2+(d.o₁:ℂ))*(z^2+(d.o₂:ℂ)) =
          (g₁:ℂ)*(z^2+(d.e₂:ℂ))*(z^2+(d.e₃:ℂ)) +
          (g₂:ℂ)*(z^2+(d.e₁:ℂ))*(z^2+(d.e₃:ℂ)) +
          (g₃:ℂ)*(z^2+(d.e₁:ℂ))*(z^2+(d.e₂:ℂ)) := by
        simpa only [g₁,g₂,g₃,ofReal_div,ofReal_mul,ofReal_sub] using hid
      field_simp [hn₁,hn₂,hn₃]
      linear_combination hz - z*hid'
    have hr := congrArg Complex.re heq
    simp only [add_re, one_re, mul_re, ofReal_re, ofReal_im, zero_mul,
      sub_zero, zero_re] at hr
    have h₁ := mul_nonneg hg₁.le (resonator_nonneg hre d.e₁_pos.le)
    have h₂ := mul_nonneg hg₂.le (resonator_nonneg hre he₂.le)
    have h₃ := mul_nonneg hg₃.le (resonator_nonneg hre he₃.le)
    change 0 ≤ g₁ * _ at h₁
    change 0 ≤ g₂ * _ at h₂
    change 0 ≤ g₃ * _ at h₃
    linarith

/-- Every denominator in the explicit independent box is Hurwitz. -/
theorem robustly_hurwitz : box.RobustlyHurwitz := by
  intro a ha
  obtain ⟨d⟩ := interlacing ha
  apply hurwitz_of_interlacing d
  have h := ha.1
  norm_num [box, lower] at h
  linarith

end
end SPR.DegreeNecessity
