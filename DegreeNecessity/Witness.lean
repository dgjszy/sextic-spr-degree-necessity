import DegreeNecessity.Squares
import DegreeNecessity.Stability

/-!
# One explicit sextic numerator works throughout the box

Every auxiliary corner pairing is nonnegative. Their sum is positive because
the contact frequencies are distinct. The contraction gives each actual corner
a positive contribution from this sum.
-/
namespace SPR.DegreeNecessity
noncomputable section
open N6

/-- Pairing with one auxiliary parity corner. -/
def boundaryPair (c : Corner) (t : ℝ) : ℝ :=
  numeratorEven witness t*(if c.1 then E₁ t else E₀ t) +
    t*numeratorOdd witness t*(if c.2 then O₁ t else O₀ t)

/-- All four auxiliary corner pairings are nonnegative on the full half-axis. -/
theorem boundary_nonneg (c : Corner) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ boundaryPair c t := by
  rcases c with ⟨i,j⟩
  cases i <;> cases j
  · change 0 ≤ numeratorEven witness t * E₀ t + t * numeratorOdd witness t * O₀ t
    rw [square0]
    exact mul_nonneg (sq_nonneg _) (F0_pos ht).le
  · change 0 ≤ numeratorEven witness t * E₀ t + t * numeratorOdd witness t * O₁ t
    rw [square1]
    exact mul_nonneg (sq_nonneg _) (F1_pos ht).le
  · change 0 ≤ numeratorEven witness t * E₁ t + t * numeratorOdd witness t * O₀ t
    rw [square2]
    exact mul_nonneg (sq_nonneg _) (F2_pos ht).le
  · change 0 ≤ numeratorEven witness t * E₁ t + t * numeratorOdd witness t * O₁ t
    rw [square3]
    exact mul_nonneg (sq_nonneg _) (F3_pos ht).le

/-- Distinct contact squares make the sum of the corner pairings strictly positive. -/
theorem boundary_sum_pos {t : ℝ} (ht : 0 ≤ t) :
    0 < boundaryPair (false,false) t + boundaryPair (false,true) t +
      boundaryPair (true,false) t + boundaryPair (true,true) t := by
  have h0 := boundary_nonneg (false,false) ht
  have h1 := boundary_nonneg (false,true) ht
  have h2 := boundary_nonneg (true,false) ht
  have h3 := boundary_nonneg (true,true) ht
  by_cases hz : t = 1000
  · have hp : 0 < boundaryPair (false,true) t := by
      change 0 < numeratorEven witness t*E₀ t+t*numeratorOdd witness t*O₁ t
      rw [square1]
      exact mul_pos (sq_pos_of_ne_zero (by rw [hz]; norm_num)) (F1_pos ht)
    linarith
  · have hp : 0 < boundaryPair (false,false) t := by
      change 0 < numeratorEven witness t*E₀ t+t*numeratorOdd witness t*O₀ t
      rw [square0]
      exact mul_pos (sq_pos_of_ne_zero (sub_ne_zero.mpr hz)) (F0_pos ht)
    linarith

/-- Exact effect of contracting the independent coefficient box. -/
theorem contracted_pairing (c : Corner) (t : ℝ) :
    pairing (box.corner c) witness t =
      (999999999/1000000000)*boundaryPair c t + (1/4000000000)*
      (boundaryPair (false,false) t + boundaryPair (false,true) t +
       boundaryPair (true,false) t + boundaryPair (true,true) t) := by
  rcases c with ⟨i,j⟩
  cases i <;> cases j <;>
    norm_num [pairing,box,lower,upper,Box6.corner,evenPart,oddPart,boundaryPair,E₀,E₁,O₀,O₁]
  all_goals ring

/-- The same explicit coefficients give strict positivity for every member and frequency. -/
theorem witness_pairing {a : Poly6} (ha : box.Contains a) {t : ℝ} (ht : 0 ≤ t) :
    0 < pairing a witness t := by
  obtain ⟨c,hc⟩ := box.exists_corner_le ha witness ht
  apply lt_of_lt_of_le _ hc
  rw [contracted_pairing]
  exact add_pos_of_nonneg_of_pos
    (mul_nonneg (by norm_num) (boundary_nonneg c ht))
    (mul_pos (by norm_num) (boundary_sum_pos ht))

/-- A fixed polynomial of actual degree six is strictly positive real for the whole box. -/
theorem witness_spr {a : Poly6} (ha : box.Contains a) :
    FrequencySPR a.toPoly (numeratorPoly witness) :=
  (frequencySPR_iff (robustly_hurwitz a ha) witness).mpr (fun _ ht => witness_pairing ha ht)

end
end SPR.DegreeNecessity
