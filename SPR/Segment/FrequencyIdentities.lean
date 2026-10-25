import SPR.Segment.Elimination

/-!
# Polynomial identities evaluated on the imaginary axis

Real coefficients intertwine complex conjugation and evaluation. A reflected
pairing identity therefore gives exactly the cleared real quotient numerator.
Positive collinearity at a crossing follows from stability of the entire segment.
-/

namespace SPR.Segment

open Polynomial Complex

noncomputable section

@[simp] theorem value_star (p : ℝ[X]) (z : ℂ) : value p (star z) = star (value p z) :=
  Polynomial.aeval_conj p z

@[simp] theorem value_add (p q : ℝ[X]) (z : ℂ) : value (p + q) z = value p z + value q z := by
  simp [value]

@[simp] theorem value_mul (p q : ℝ[X]) (z : ℂ) : value (p * q) z = value p z * value q z := by
  simp [value]

@[simp] theorem value_C (x : ℝ) (z : ℂ) : value (C x) z = (x : ℂ) := by
  simp [value]

@[simp] theorem value_frequencyLift (H : ℝ[X]) (ω : ℝ) :
    value (frequencyLift H) (I * (ω : ℂ)) = Complex.ofReal (H.eval (ω ^ 2)) := by
  have he : -(I * (ω : ℂ)) ^ 2 = ((ω ^ 2 : ℝ) : ℂ) := by
    simp [mul_pow]
  simp only [value, frequencyLift, eval₂_comp, eval₂_neg, eval₂_pow, eval₂_X, he]
  exact Polynomial.aeval_ofReal (K := ℂ) H (ω ^ 2)

/-- A symmetric polynomial identity is exactly the imaginary-axis real pairing. -/
theorem pairing_of_identity {p c H : ℝ[X]}
    (h : c * reflect p + reflect c * p = C 2 * frequencyLift H) (ω : ℝ) :
    pairing p c ω = H.eval (ω ^ 2) := by
  have he := congrArg (fun q : ℝ[X] => (value q (I * (ω : ℂ))).re) h
  have hstar : -(I * (ω : ℂ)) = star (I * (ω : ℂ)) := by simp
  simp only [value_add, value_mul, value_reflect, hstar, value_star,
    value_C, value_frequencyLift] at he
  simp only [Complex.add_re, Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero] at he
  unfold pairing
  simp only [Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im]
  linarith

/-- An identity with a nonzero right hand side guarantees a nonzero numerator. -/
theorem numerator_ne_zero_of_identity {p c H : ℝ[X]} (hH : frequencyLift H ≠ 0)
    (h : c * reflect p + reflect c * p = C 2 * frequencyLift H) : c ≠ 0 := by
  intro hc
  have hh : C (2 : ℝ) * frequencyLift H = 0 := by simpa [hc, reflect] using h.symm
  exact hH ((mul_eq_zero.mp hh).resolve_left (by simp))

/-- A real collinearity factor at a point of the closed right half-plane is positive;
a nonpositive factor would make a stable segment member vanish there. -/
theorem collinear_ratio_pos {p₀ p₁ : ℝ[X]} (hs : Stable p₀ p₁)
    {z : ℂ} (hz : 0 ≤ z.re) {ρ : ℝ}
    (hρ : value p₁ z = (ρ : ℂ) * value p₀ z) : 0 < ρ := by
  have hne₁ := value_ne_zero hs.right hz
  have hρne : ρ ≠ 0 := by
    intro he
    have hh : value p₁ z = 0 := by simpa only [he, ofReal_zero, zero_mul] using hρ
    exact hne₁ hh
  by_contra hn
  have hneg : ρ < 0 := lt_of_le_of_ne (le_of_not_gt hn) hρne
  have hden : 0 < 1 - ρ := by linarith
  let θ : ℝ := 1 / (1 - ρ)
  have hθ : θ ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · exact (div_pos zero_lt_one hden).le
    · exact (div_le_one hden).mpr (by linarith)
  have hzero : value (blend p₀ p₁ θ) z = 0 := by
    rw [value_blend, hρ]
    have hscalar : 1 - θ + θ * ρ = 0 := by dsimp [θ]; field_simp; ring
    have hc : ((1 - θ : ℝ) : ℂ) + (θ : ℂ) * (ρ : ℂ) = 0 := by
      exact_mod_cast hscalar
    calc
      _ = (((1 - θ : ℝ) : ℂ) + (θ : ℂ) * (ρ : ℂ)) * value p₀ z := by ring
      _ = 0 := by rw [hc]; simp
  exact value_ne_zero (hs θ hθ) hz hzero

end
end SPR.Segment
