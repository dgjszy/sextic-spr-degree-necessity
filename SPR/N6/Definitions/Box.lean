import SPR.N6.Definitions.Frequency

/-!
# Actual box corners and pointwise extrema

All four parity combinations below are members of the original independent
coefficient box. The minimum pairing corner can depend on frequency; the
numerator remains fixed. No Kharitonov or synthesis theorem is assumed.
-/
namespace SPR.N6
noncomputable section

/-- First bit selects the even upper endpoint; second bit selects the odd upper endpoint. -/
abbrev Corner := Bool × Bool

def Box6.evenLower (K : Box6) (t : ℝ) : ℝ :=
  -t ^ 3 + K.lower.a2 * t ^ 2 - K.upper.a4 * t + K.lower.a6

def Box6.evenUpper (K : Box6) (t : ℝ) : ℝ :=
  -t ^ 3 + K.upper.a2 * t ^ 2 - K.lower.a4 * t + K.upper.a6

def Box6.oddLower (K : Box6) (t : ℝ) : ℝ :=
  K.lower.a1 * t ^ 2 - K.upper.a3 * t + K.lower.a5

def Box6.oddUpper (K : Box6) (t : ℝ) : ℝ :=
  K.upper.a1 * t ^ 2 - K.lower.a3 * t + K.upper.a5

/-- Actual simultaneous even and odd coefficient endpoints. -/
def Box6.corner (K : Box6) (c : Corner) : Poly6 :=
  ⟨if c.2 then K.upper.a1 else K.lower.a1,
   if c.1 then K.upper.a2 else K.lower.a2,
   if c.2 then K.lower.a3 else K.upper.a3,
   if c.1 then K.lower.a4 else K.upper.a4,
   if c.2 then K.upper.a5 else K.lower.a5,
   if c.1 then K.upper.a6 else K.lower.a6⟩

theorem Box6.corner_mem (K : Box6) (c : Corner) : K.Contains (K.corner c) := by
  rcases c with ⟨i, j⟩
  cases i <;> cases j <;>
    simp [Contains, corner, K.h1, K.h2, K.h3, K.h4, K.h5, K.h6]

theorem Box6.lower_mem (K : Box6) : K.Contains K.lower := by
  simp [Contains, K.h1, K.h2, K.h3, K.h4, K.h5, K.h6]

theorem Box6.upper_mem (K : Box6) : K.Contains K.upper := by
  simp [Contains, K.h1, K.h2, K.h3, K.h4, K.h5, K.h6]

theorem Box6.even_corner (K : Box6) (c : Corner) (t : ℝ) :
    evenPart (K.corner c) t = if c.1 then K.evenUpper t else K.evenLower t := by
  rcases c with ⟨i, j⟩
  cases i <;> cases j <;> rfl

theorem Box6.odd_corner (K : Box6) (c : Corner) (t : ℝ) :
    oddPart (K.corner c) t = if c.2 then K.oddUpper t else K.oddLower t := by
  rcases c with ⟨i, j⟩
  cases i <;> cases j <;> rfl

theorem Box6.component_bounds {K : Box6} {a : Poly6} (ha : K.Contains a)
    {t : ℝ} (ht : 0 ≤ t) :
    K.evenLower t ≤ evenPart a t ∧ evenPart a t ≤ K.evenUpper t ∧
      K.oddLower t ≤ oddPart a t ∧ oddPart a t ≤ K.oddUpper t := by
  rcases ha with ⟨h1l, h1u, h2l, h2u, h3l, h3u, h4l, h4u, h5l, h5u, h6l, h6u⟩
  unfold evenLower evenUpper oddLower oddUpper evenPart oddPart
  refine ⟨?_, ?_, ?_, ?_⟩
  · nlinarith only [mul_nonneg (sub_nonneg.mpr h2l) (sq_nonneg t),
      mul_nonneg (sub_nonneg.mpr h4u) ht, h6l]
  · nlinarith only [mul_nonneg (sub_nonneg.mpr h2u) (sq_nonneg t),
      mul_nonneg (sub_nonneg.mpr h4l) ht, h6u]
  · nlinarith only [mul_nonneg (sub_nonneg.mpr h1l) (sq_nonneg t),
      mul_nonneg (sub_nonneg.mpr h3u) ht, h5l]
  · nlinarith only [mul_nonneg (sub_nonneg.mpr h1u) (sq_nonneg t),
      mul_nonneg (sub_nonneg.mpr h3l) ht, h5u]

/-- For each squared frequency, choose the minimizing actual parity corner. -/
theorem Box6.exists_corner_le {K : Box6} {a : Poly6} (ha : K.Contains a)
    (b : Vec7) {t : ℝ} (ht : 0 ≤ t) :
    ∃ c : Corner, pairing (K.corner c) b t ≤ pairing a b t := by
  rcases K.component_bounds ha ht with ⟨hel, heu, hol, hou⟩
  by_cases he : 0 ≤ numeratorEven b t
  · have hE := mul_le_mul_of_nonneg_left hel he
    by_cases ho : 0 ≤ numeratorOdd b t
    · exact ⟨(false, false), add_le_add hE
        (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hol ho) ht)⟩
    · exact ⟨(false, true), add_le_add hE
        (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonpos_left hou (le_of_not_ge ho)) ht)⟩
  · have hE := mul_le_mul_of_nonpos_left heu (le_of_not_ge he)
    by_cases ho : 0 ≤ numeratorOdd b t
    · exact ⟨(true, false), add_le_add hE
        (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hol ho) ht)⟩
    · exact ⟨(true, true), add_le_add hE
        (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonpos_left hou (le_of_not_ge ho)) ht)⟩

/-- Four-corner equivalence for an arbitrary fixed, unrestricted numerator. -/
theorem Box6.pairing_pos_iff_corners (K : Box6) (b : Vec7) :
    (∀ a : Poly6, K.Contains a → ∀ t : ℝ, 0 ≤ t → 0 < pairing a b t) ↔
      ∀ c : Corner, ∀ t : ℝ, 0 ≤ t → 0 < pairing (K.corner c) b t := by
  constructor
  · intro h c
    exact h _ (K.corner_mem c)
  · intro h a ha t ht
    obtain ⟨c, hc⟩ := K.exists_corner_le ha b ht
    exact lt_of_lt_of_le (h c t ht) hc

/-- The four actual corners suffice for the original all-frequency ratio condition. -/
theorem Box6.frequencySPR_iff_corners (K : Box6) (hK : K.RobustlyHurwitz) (b : Vec7) :
    (∀ a : Poly6, K.Contains a → FrequencySPR a.toPoly (numeratorPoly b)) ↔
      ∀ c : Corner, FrequencySPR (K.corner c).toPoly (numeratorPoly b) := by
  constructor
  · intro h c
    exact h _ (K.corner_mem c)
  · intro h a ha
    apply (frequencySPR_iff (hK a ha) b).mpr
    apply (K.pairing_pos_iff_corners b).mpr ?_ a ha
    intro c
    exact (frequencySPR_iff (hK _ (K.corner_mem c)) b).mp (h c)

end
end SPR.N6
