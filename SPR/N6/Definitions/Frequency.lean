import SPR.Common.Hurwitz

/-!
# Exact sixth-order interval statement and frequency algebra

Closed real coefficient intervals include all degenerate cases. The numerator
is unrestricted except for exact degree six; the same numerator must work on
the entire box at every finite real frequency. `RobustSPRStatement` is a
proposition, not a theorem asserting synthesis.
-/
namespace SPR.N6
noncomputable section
open Polynomial Complex

/-- Six coefficients of a real monic sextic, in descending order. -/
structure Poly6 where
  a1 : ℝ
  a2 : ℝ
  a3 : ℝ
  a4 : ℝ
  a5 : ℝ
  a6 : ℝ

/-- The monic sextic represented by its coefficients. -/
def Poly6.toPoly (p : Poly6) : ℝ[X] :=
  X ^ 6 + C p.a1 * X ^ 5 + C p.a2 * X ^ 4 + C p.a3 * X ^ 3 +
    C p.a4 * X ^ 2 + C p.a5 * X + C p.a6

/-- A closed coefficient box with ordered, finite real endpoints. -/
structure Box6 where
  lower : Poly6
  upper : Poly6
  h1 : lower.a1 ≤ upper.a1
  h2 : lower.a2 ≤ upper.a2
  h3 : lower.a3 ≤ upper.a3
  h4 : lower.a4 ≤ upper.a4
  h5 : lower.a5 ≤ upper.a5
  h6 : lower.a6 ≤ upper.a6

/-- All six independent coefficient constraints. -/
def Box6.Contains (K : Box6) (a : Poly6) : Prop :=
  K.lower.a1 ≤ a.a1 ∧ a.a1 ≤ K.upper.a1 ∧
  K.lower.a2 ≤ a.a2 ∧ a.a2 ≤ K.upper.a2 ∧
  K.lower.a3 ≤ a.a3 ∧ a.a3 ≤ K.upper.a3 ∧
  K.lower.a4 ≤ a.a4 ∧ a.a4 ≤ K.upper.a4 ∧
  K.lower.a5 ≤ a.a5 ∧ a.a5 ≤ K.upper.a5 ∧
  K.lower.a6 ≤ a.a6 ∧ a.a6 ≤ K.upper.a6

/-- Every member of the original coefficient box is strictly Hurwitz. -/
def Box6.RobustlyHurwitz (K : Box6) : Prop :=
  ∀ a : Poly6, K.Contains a → IsHurwitz a.toPoly

/-- Strict positivity at every finite real frequency, with no extra hypothesis. -/
def FrequencySPR (a b : ℝ[X]) : Prop :=
  ∀ ω : ℝ, 0 < (eval (I * (ω : ℂ)) (b.map (algebraMap ℝ ℂ)) /
    eval (I * (ω : ℂ)) (a.map (algebraMap ℝ ℂ))).re

/-- The original sixth-order target, including degenerate intervals. -/
def RobustSPRStatement : Prop :=
  ∀ K : Box6, K.RobustlyHurwitz →
    ∃ b : ℝ[X], b.natDegree = 6 ∧ ∀ a : Poly6, K.Contains a → FrequencySPR a.toPoly b

/-- Cubic even part on the squared-frequency axis. -/
def evenPart (a : Poly6) (t : ℝ) : ℝ := -t ^ 3 + a.a2 * t ^ 2 - a.a4 * t + a.a6

/-- Quadratic odd part on the squared-frequency axis. -/
def oddPart (a : Poly6) (t : ℝ) : ℝ := a.a1 * t ^ 2 - a.a3 * t + a.a5

/-- Polynomial form of the even part. -/
def evenPoly (a : Poly6) : ℝ[X] := -X ^ 3 + C a.a2 * X ^ 2 - C a.a4 * X + C a.a6

/-- Polynomial form of the odd part. -/
def oddPoly (a : Poly6) : ℝ[X] := C a.a1 * X ^ 2 - C a.a3 * X + C a.a5

/-- The actual denominator on the imaginary axis. -/
def frequencyValue (a : Poly6) (ω : ℝ) : ℂ :=
  eval (I * (ω : ℂ)) (a.toPoly.map (algebraMap ℝ ℂ))

theorem sextic_natDegree (a : Poly6) : a.toPoly.natDegree = 6 := by
  unfold Poly6.toPoly
  compute_degree!

theorem sextic_monic (a : Poly6) : a.toPoly.Monic := by
  unfold Poly6.toPoly
  monicity!

theorem sextic_coefficients_pos {a : Poly6} (ha : IsHurwitz a.toPoly) :
    0 < a.a1 ∧ 0 < a.a2 ∧ 0 < a.a3 ∧ 0 < a.a4 ∧ 0 < a.a5 ∧ 0 < a.a6 := by
  have hlc : 0 < a.toPoly.leadingCoeff := by rw [(sextic_monic a).leadingCoeff]; norm_num
  have h (n : ℕ) (hn : n ≤ 6) : 0 < a.toPoly.coeff n :=
    Hurwitz.hurwitz_coeff_pos ha hlc n (by rwa [sextic_natDegree])
  have h1 := h 5 (by omega)
  have h2 := h 4 (by omega)
  have h3 := h 3 (by omega)
  have h4 := h 2 (by omega)
  have h5 := h 1 (by omega)
  have h6 := h 0 (by omega)
  norm_num [Poly6.toPoly, coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X]
    at h1 h2 h3 h4 h5 h6
  exact ⟨h1, h2, h3, h4, h5, h6⟩

theorem frequencyValue_eq (a : Poly6) (ω : ℝ) :
    frequencyValue a ω = (evenPart a (ω ^ 2) : ℂ) +
      I * (ω : ℂ) * (oddPart a (ω ^ 2) : ℂ) := by
  simp only [frequencyValue, Poly6.toPoly, Polynomial.map_add, Polynomial.map_mul,
    Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C,
    evenPart, oddPart, ofReal_add, ofReal_sub, ofReal_mul, ofReal_pow, ofReal_neg]
  apply Complex.ext <;> simp [pow_succ, Complex.mul_re, Complex.mul_im] <;> ring

theorem frequencyValue_re (a : Poly6) (ω : ℝ) :
    (frequencyValue a ω).re = evenPart a (ω ^ 2) := by rw [frequencyValue_eq]; simp

theorem frequencyValue_im (a : Poly6) (ω : ℝ) :
    (frequencyValue a ω).im = ω * oddPart a (ω ^ 2) := by rw [frequencyValue_eq]; simp

theorem hurwitz_frequencyValue_ne_zero {a : Poly6} (ha : IsHurwitz a.toPoly) (ω : ℝ) :
    frequencyValue a ω ≠ 0 := by
  intro hz
  have hh := ha (I * (ω : ℂ)) hz
  simp at hh

/-- Seven arbitrary numerator coefficients, from degree six to the constant. -/
abbrev Vec7 := Fin 7 → ℝ

def numeratorPoly (b : Vec7) : ℝ[X] :=
  C (b 0) * X ^ 6 + C (b 1) * X ^ 5 + C (b 2) * X ^ 4 + C (b 3) * X ^ 3 +
    C (b 4) * X ^ 2 + C (b 5) * X + C (b 6)

def numeratorEven (b : Vec7) (t : ℝ) : ℝ := -b 0 * t ^ 3 + b 2 * t ^ 2 - b 4 * t + b 6

def numeratorOdd (b : Vec7) (t : ℝ) : ℝ := b 1 * t ^ 2 - b 3 * t + b 5

/-- Real numerator of the frequency ratio before division by the positive norm square. -/
def pairing (a : Poly6) (b : Vec7) (t : ℝ) : ℝ :=
  numeratorEven b t * evenPart a t + t * (numeratorOdd b t * oddPart a t)

theorem numeratorPoly_degree (b : Vec7) (hb : b 0 ≠ 0) :
    (numeratorPoly b).natDegree = 6 := by
  unfold numeratorPoly
  compute_degree!

theorem numerator_frequency_eq (b : Vec7) (ω : ℝ) :
    eval (I * (ω : ℂ)) ((numeratorPoly b).map (algebraMap ℝ ℂ)) =
      (numeratorEven b (ω ^ 2) : ℂ) + I * (ω : ℂ) * (numeratorOdd b (ω ^ 2) : ℂ) := by
  simp only [numeratorPoly, Polynomial.map_add, Polynomial.map_mul,
    Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C,
    numeratorEven, numeratorOdd, ofReal_add, ofReal_sub, ofReal_mul, ofReal_pow, ofReal_neg]
  apply Complex.ext <;> simp [pow_succ, Complex.mul_re, Complex.mul_im] <;> ring

theorem real_ratio_eq (a : Poly6) (b : Vec7) (ω : ℝ) :
    (eval (I * (ω : ℂ)) ((numeratorPoly b).map (algebraMap ℝ ℂ)) /
      frequencyValue a ω).re = pairing a b (ω ^ 2) / Complex.normSq (frequencyValue a ω) := by
  rw [Complex.div_re, frequencyValue_re, frequencyValue_im, numerator_frequency_eq]
  simp only [add_re, ofReal_re, mul_re, I_re, mul_im, I_im, ofReal_im,
    zero_mul, one_mul, mul_zero, sub_zero, zero_add, add_im, add_zero]
  unfold pairing
  rw [← add_div]
  congr 1
  ring

/-- Exact equivalence with all nonnegative squared frequencies. -/
theorem frequencySPR_iff {a : Poly6} (ha : IsHurwitz a.toPoly) (b : Vec7) :
    FrequencySPR a.toPoly (numeratorPoly b) ↔ ∀ t : ℝ, 0 ≤ t → 0 < pairing a b t := by
  have hω (ω : ℝ) :
      0 < (eval (I * (ω : ℂ)) ((numeratorPoly b).map (algebraMap ℝ ℂ)) /
        frequencyValue a ω).re ↔ 0 < pairing a b (ω ^ 2) := by
    rw [real_ratio_eq]
    exact div_pos_iff_of_pos_right
      (Complex.normSq_pos.mpr (hurwitz_frequencyValue_ne_zero ha ω))
  constructor
  · intro h t ht
    simpa only [Real.sq_sqrt ht] using (hω (Real.sqrt t)).mp (h (Real.sqrt t))
  · intro h ω
    exact (hω ω).mpr (h (ω ^ 2) (sq_nonneg ω))

end
end SPR.N6
