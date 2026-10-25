import SPR.Common.Hurwitz

/-!
# The arbitrary-order stable-segment SPR problem

The parameter is one shared real number in the closed unit interval. The numerator
is chosen once, before both the segment parameter and the real frequency.
No independent coefficient box or extra condition at infinity is part of this definition.
-/

namespace SPR.Segment

open Polynomial Complex

noncomputable section

/-- The real polynomial at a point of the closed segment between two endpoints. -/
def blend (a₀ a₁ : ℝ[X]) (θ : ℝ) : ℝ[X] :=
  (1 - θ) • a₀ + θ • a₁

/-- Complex evaluation of a real polynomial. -/
def value (p : ℝ[X]) (z : ℂ) : ℂ :=
  p.eval₂ (algebraMap ℝ ℂ) z

/-- The real numerator of the real part after clearing the positive squared norm. -/
def pairing (a b : ℝ[X]) (ω : ℝ) : ℝ :=
  (value b (I * (ω : ℂ)) * star (value a (I * (ω : ℂ)))).re

/-- Strict positivity on the entire finite imaginary axis. -/
def FrequencySPR (a b : ℝ[X]) : Prop :=
  ∀ ω : ℝ, 0 < (value b (I * (ω : ℂ)) / value a (I * (ω : ℂ))).re

/-- Every member of the closed polynomial segment is strictly Hurwitz. -/
def Stable (a₀ a₁ : ℝ[X]) : Prop :=
  ∀ θ ∈ Set.Icc (0 : ℝ) 1, IsHurwitz (blend a₀ a₁ θ)

/-- The exact target: arbitrary positive order and one real numerator of exactly that order. -/
def RobustSPRStatement : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ a₀ a₁ : ℝ[X],
    a₀.Monic → a₁.Monic → a₀.natDegree = n → a₁.natDegree = n →
    Stable a₀ a₁ →
    ∃ b : ℝ[X], b.natDegree = n ∧
      ∀ θ ∈ Set.Icc (0 : ℝ) 1, FrequencySPR (blend a₀ a₁ θ) b

@[simp] theorem blend_zero (a₀ a₁ : ℝ[X]) : blend a₀ a₁ 0 = a₀ := by
  simp [blend]

@[simp] theorem blend_one (a₀ a₁ : ℝ[X]) : blend a₀ a₁ 1 = a₁ := by
  simp [blend]

@[simp] theorem blend_self (a : ℝ[X]) (θ : ℝ) : blend a a θ = a := by
  rw [blend, ← add_smul]
  simp

theorem Stable.left {a₀ a₁ : ℝ[X]} (h : Stable a₀ a₁) : IsHurwitz a₀ := by
  simpa using h 0 ⟨le_rfl, zero_le_one⟩

theorem Stable.right {a₀ a₁ : ℝ[X]} (h : Stable a₀ a₁) : IsHurwitz a₁ := by
  simpa using h 1 ⟨zero_le_one, le_rfl⟩

theorem value_ne_zero {a : ℝ[X]} (ha : IsHurwitz a) {z : ℂ}
    (hz : 0 ≤ z.re) : value a z ≠ 0 := by
  intro hzero
  have hroot : (a.map (algebraMap ℝ ℂ)).IsRoot z := by
    simpa [IsRoot, value, eval_map] using hzero
  exact (not_lt_of_ge hz) (ha z hroot)

@[simp] theorem value_blend (a₀ a₁ : ℝ[X]) (θ : ℝ) (z : ℂ) :
    value (blend a₀ a₁ θ) z =
      ((1 - θ : ℝ) : ℂ) * value a₀ z + (θ : ℂ) * value a₁ z := by
  simp [value, blend, smul_eq_C_mul]

/-- Clearing the denominator preserves the sign because the denominator is nonzero. -/
theorem real_ratio (a b : ℝ[X]) (ω : ℝ) :
    (value b (I * (ω : ℂ)) / value a (I * (ω : ℂ))).re =
      pairing a b ω / Complex.normSq (value a (I * (ω : ℂ))) := by
  simp [pairing, Complex.div_re, Complex.mul_re, ← add_div]

theorem frequencySPR_iff_pairing_pos {a b : ℝ[X]} (ha : IsHurwitz a) :
    FrequencySPR a b ↔ ∀ ω : ℝ, 0 < pairing a b ω := by
  have hnorm (ω : ℝ) : 0 < Complex.normSq (value a (I * (ω : ℂ))) :=
    Complex.normSq_pos.mpr (value_ne_zero ha (by simp))
  simp only [FrequencySPR, real_ratio, div_pos_iff_of_pos_right (hnorm _)]

/-- The cleared real part, rather than the rational quotient, is affine in the denominator. -/
theorem pairing_blend (a₀ a₁ b : ℝ[X]) (θ ω : ℝ) :
    pairing (blend a₀ a₁ θ) b ω =
      (1 - θ) * pairing a₀ b ω + θ * pairing a₁ b ω := by
  simp [pairing, Complex.mul_re, Complex.mul_im]
  ring

/-- Two strict endpoint inequalities imply strict positivity for every stable segment member. -/
theorem frequencySPR_blend {a₀ a₁ b : ℝ[X]} (hs : Stable a₀ a₁)
    (h₀ : FrequencySPR a₀ b) (h₁ : FrequencySPR a₁ b)
    {θ : ℝ} (hθ : θ ∈ Set.Icc (0 : ℝ) 1) : FrequencySPR (blend a₀ a₁ θ) b := by
  rw [frequencySPR_iff_pairing_pos (hs θ hθ)]
  intro ω
  have hp₀ := (frequencySPR_iff_pairing_pos hs.left).mp h₀ ω
  have hp₁ := (frequencySPR_iff_pairing_pos hs.right).mp h₁ ω
  rw [pairing_blend]
  by_cases hz : θ = 0
  · simpa [hz] using hp₀
  · exact add_pos_of_nonneg_of_pos
      (mul_nonneg (sub_nonneg.mpr hθ.2) hp₀.le)
      (mul_pos (lt_of_le_of_ne hθ.1 (Ne.symm hz)) hp₁)

/-- The coincident-endpoint case already has an exact-degree witness. -/
theorem synthesis_self {a : ℝ[X]} (ha : IsHurwitz a) : FrequencySPR a a := by
  intro ω
  rw [div_self (value_ne_zero ha (by simp))]
  simp

end
end SPR.Segment
