import SPR.Segment.Definitions

/-!
# Reflection and exact elimination

The cross polynomial of two distinct equal-degree monic Hurwitz polynomials is
nonzero. Once polynomial divisibility has produced a quotient, two cleared
identities recover its real pairings. This module never uses a rational quotient
as a polynomial or assumes simplicity of the cross polynomial's roots.
-/

namespace SPR.Segment

open Polynomial Complex

noncomputable section

/-- Substitution `s ↦ -s`. -/
def reflect (p : ℝ[X]) : ℝ[X] := p.comp (-X)

/-- Substitution from the squared-frequency variable, `t ↦ -s²`. -/
def frequencyLift (p : ℝ[X]) : ℝ[X] := p.comp (-(X ^ 2))

/-- The odd cross polynomial of the two denominator endpoints. -/
def cross (p₀ p₁ : ℝ[X]) : ℝ[X] := reflect p₀ * p₁ - p₀ * reflect p₁

@[simp] theorem reflect_add (p q : ℝ[X]) : reflect (p + q) = reflect p + reflect q := by
  simp [reflect]

@[simp] theorem reflect_sub (p q : ℝ[X]) : reflect (p - q) = reflect p - reflect q := by
  simp [reflect]

@[simp] theorem reflect_mul (p q : ℝ[X]) : reflect (p * q) = reflect p * reflect q := by
  simp [reflect]

@[simp] theorem reflect_C (x : ℝ) : reflect (C x) = C x := by
  simp [reflect]

@[simp] theorem reflect_reflect (p : ℝ[X]) : reflect (reflect p) = p := by
  simp [reflect, comp_assoc]

@[simp] theorem reflect_frequencyLift (p : ℝ[X]) :
    reflect (frequencyLift p) = frequencyLift p := by
  simp [reflect, frequencyLift, comp_assoc]

@[simp] theorem reflect_cross (p₀ p₁ : ℝ[X]) :
    reflect (cross p₀ p₁) = -cross p₀ p₁ := by
  simp [cross]

@[simp] theorem value_reflect (p : ℝ[X]) (z : ℂ) : value (reflect p) z = value p (-z) := by
  simp [reflect, value, eval₂_comp]

theorem hurwitz_coprime_reflect {p q : ℝ[X]} (hp : IsHurwitz p) (hq : IsHurwitz q) :
    IsCoprime p (reflect q) := by
  apply (Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed ℝ ℂ p (reflect q)).mpr
  intro z
  by_contra h
  push Not at h
  have hpz : z.re < 0 := hp z (by simpa [IsRoot, eval_map, value] using h.1)
  have hqr : value (reflect q) z = 0 := h.2
  rw [value_reflect] at hqr
  have hqz : (-z).re < 0 := hq (-z) (by
    simpa [IsRoot, eval_map, value] using hqr)
  simp only [neg_re] at hqz
  linarith

/-- Stable endpoints of the same monic degree have a nonzero cross unless they coincide. -/
theorem cross_ne_zero {p₀ p₁ : ℝ[X]} (h₀ : IsHurwitz p₀) (_h₁ : IsHurwitz p₁)
    (hm₀ : p₀.Monic) (hm₁ : p₁.Monic) (hdeg : p₀.natDegree = p₁.natDegree)
    (hne : p₀ ≠ p₁) : cross p₀ p₁ ≠ 0 := by
  intro hz
  have he : reflect p₀ * p₁ = p₀ * reflect p₁ := sub_eq_zero.mp hz
  have hd : p₀ ∣ reflect p₀ * p₁ := by rw [he]; exact dvd_mul_right _ _
  have hp : p₀ ∣ p₁ := (hurwitz_coprime_reflect h₀ h₀).dvd_of_dvd_mul_left hd
  exact hne (eq_of_monic_of_dvd_of_natDegree_le hm₀ hm₁ hp hdeg.ge).symm

/-- Reflection of the quotient identity, with the sign of the odd denominator explicit. -/
theorem reflected_quotient_identity {p₀ p₁ c H₀ H₁ : ℝ[X]}
    (hc : cross p₀ p₁ * c =
      C 2 * (frequencyLift H₀ * p₁ - frequencyLift H₁ * p₀)) :
    -cross p₀ p₁ * reflect c =
      C 2 * (frequencyLift H₀ * reflect p₁ - frequencyLift H₁ * reflect p₀) := by
  simpa only [reflect_mul, reflect_sub, reflect_cross, reflect_C,
    reflect_frequencyLift] using congrArg reflect hc

/-- The quotient identity recovers the first pairing by cancellation of a nonzero polynomial. -/
theorem elimination_left {p₀ p₁ c H₀ H₁ : ℝ[X]} (hd : cross p₀ p₁ ≠ 0)
    (hc : cross p₀ p₁ * c =
      C 2 * (frequencyLift H₀ * p₁ - frequencyLift H₁ * p₀)) :
    c * reflect p₀ + reflect c * p₀ = C 2 * frequencyLift H₀ := by
  have hr := reflected_quotient_identity hc
  apply mul_left_cancel₀ hd
  dsimp [cross] at hc hr ⊢
  linear_combination reflect p₀ * hc - p₀ * hr

/-- The same polynomial quotient recovers the second endpoint pairing. -/
theorem elimination_right {p₀ p₁ c H₀ H₁ : ℝ[X]} (hd : cross p₀ p₁ ≠ 0)
    (hc : cross p₀ p₁ * c =
      C 2 * (frequencyLift H₀ * p₁ - frequencyLift H₁ * p₀)) :
    c * reflect p₁ + reflect c * p₁ = C 2 * frequencyLift H₁ := by
  have hr := reflected_quotient_identity hc
  apply mul_left_cancel₀ hd
  dsimp [cross] at hc hr ⊢
  linear_combination reflect p₁ * hc - p₁ * hr

end
end SPR.Segment
