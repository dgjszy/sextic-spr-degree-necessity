import DegreeNecessity.Basic
import SPR.N6.Preliminaries.HermiteBiehler

/-!
# Strict interlacing throughout the explicit box

The signs at six rational gates give three even roots and two odd roots in
separated open intervals. Degree bounds turn these roots into factorizations.
-/
namespace SPR.DegreeNecessity
noncomputable section
open Polynomial N6

/-- A strict sign change supplies a root in the open interval. -/
theorem root_between {f : ℝ → ℝ} (hf : Continuous f) {x y : ℝ}
    (hxy : x < y) (hx : f x < 0) (hy : 0 < f y) :
    ∃ r, x < r ∧ r < y ∧ f r = 0 := by
  obtain ⟨r, hr, hz⟩ := intermediate_value_Icc hxy.le hf.continuousOn ⟨hx.le, hy.le⟩
  refine ⟨r, lt_of_le_of_ne hr.1 ?_, lt_of_le_of_ne hr.2 ?_, hz⟩
  · intro h; subst r; linarith
  · intro h; subst r; linarith

/-- Reversing the signs does not change the root interval. -/
theorem root_between' {f : ℝ → ℝ} (hf : Continuous f) {x y : ℝ}
    (hxy : x < y) (hx : 0 < f x) (hy : f y < 0) :
    ∃ r, x < r ∧ r < y ∧ f r = 0 := by
  obtain ⟨r, hr, hr', hz⟩ := root_between hf.neg hxy (neg_neg_of_pos hx) (neg_pos.mpr hy)
  exact ⟨r, hr, hr', neg_eq_zero.mp hz⟩

/-- The entire box lies strictly between each pair of frequency endpoints. -/
theorem gate_signs {a : Poly6} (ha : box.Contains a) :
    0 < evenPart a (1/10) ∧ evenPart a 1 < 0 ∧ evenPart a 3 < 0 ∧
    0 < evenPart a 20 ∧ 0 < evenPart a 1000 ∧ evenPart a 1020 < 0 ∧
    0 < oddPart a 1 ∧ oddPart a 3 < 0 ∧ oddPart a 20 < 0 ∧
    0 < oddPart a 1000 := by
  have h01 := box.component_bounds ha (t := 1/10) (by norm_num)
  have h1 := box.component_bounds ha (t := 1) (by norm_num)
  have h3 := box.component_bounds ha (t := 3) (by norm_num)
  have h20 := box.component_bounds ha (t := 20) (by norm_num)
  have h1000 := box.component_bounds ha (t := 1000) (by norm_num)
  have h1020 := box.component_bounds ha (t := 1020) (by norm_num)
  norm_num [box, lower, upper, Box6.evenLower, Box6.evenUpper,
    Box6.oddLower, Box6.oddUpper] at h01 h1 h3 h20 h1000 h1020
  exact ⟨lt_of_lt_of_le (by norm_num) h01.1,
    lt_of_le_of_lt h1.2.1 (by norm_num), lt_of_le_of_lt h3.2.1 (by norm_num),
    lt_of_lt_of_le (by norm_num) h20.1, lt_of_lt_of_le (by norm_num) h1000.1,
    lt_of_le_of_lt h1020.2.1 (by norm_num), lt_of_lt_of_le (by norm_num) h1.2.2.1,
    lt_of_le_of_lt h3.2.2.2 (by norm_num), lt_of_le_of_lt h20.2.2.2 (by norm_num),
    lt_of_lt_of_le (by norm_num) h1000.2.2.1⟩

/-- All members have strict positive interlacing, proved without assuming stability. -/
theorem interlacing {a : Poly6} (ha : box.Contains a) :
    Nonempty (DenominatorInterlacing a) := by
  rcases gate_signs ha with ⟨h01,h1,h3,h20,h1000,h1020,ho1,ho3,ho20,ho1000⟩
  have hcE : Continuous (evenPart a) := by unfold evenPart; fun_prop
  have hcO : Continuous (oddPart a) := by unfold oddPart; fun_prop
  obtain ⟨e₁,he₁,he₁',hE₁⟩ := root_between' hcE (by norm_num : (1:ℝ)/10 < 1) h01 h1
  obtain ⟨e₂,he₂,he₂',hE₂⟩ := root_between hcE (by norm_num : (3:ℝ) < 20) h3 h20
  obtain ⟨e₃,he₃,he₃',hE₃⟩ := root_between' hcE (by norm_num : (1000:ℝ) < 1020) h1000 h1020
  obtain ⟨o₁,ho₁,ho₁',hO₁⟩ := root_between' hcO (by norm_num : (1:ℝ) < 3) ho1 ho3
  obtain ⟨o₂,ho₂,ho₂',hO₂⟩ := root_between hcO (by norm_num : (20:ℝ) < 1000) ho20 ho1000
  have hEe (t : ℝ) : (evenPoly a).eval t = evenPart a t := by simp [evenPoly, evenPart]
  have hOo (t : ℝ) : (oddPoly a).eval t = oddPart a t := by simp [oddPoly, oddPart]
  have hEf := cubic_factor_of_three_roots
    (show (evenPoly a).natDegree ≤ 3 by unfold evenPoly; compute_degree!)
    (show e₁ ≠ e₂ by linarith) (show e₁ ≠ e₃ by linarith) (show e₂ ≠ e₃ by linarith)
    (by rwa [hEe]) (by rwa [hEe]) (by rwa [hEe])
  have hOf := quadratic_factor_of_two_roots
    (show (oddPoly a).natDegree ≤ 2 by unfold oddPoly; compute_degree!)
    (show o₁ ≠ o₂ by linarith) (by rwa [hOo]) (by rwa [hOo])
  refine ⟨⟨e₁,o₁,e₂,o₂,e₃,by linarith,by linarith,by linarith,
    by linarith,by linarith,?_,?_⟩⟩
  · simpa [evenPoly, coeff_sub, coeff_add, coeff_C_mul_X_pow] using hEf
  · simpa [oddPoly, coeff_sub, coeff_add, coeff_C_mul_X_pow] using hOf

end
end SPR.DegreeNecessity
