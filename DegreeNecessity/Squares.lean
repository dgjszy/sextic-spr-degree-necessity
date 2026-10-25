import DegreeNecessity.Basic

/-!
# Static square certificates for the fixed sextic numerator

Every displayed rational identity is proved by Lean's ring normalizer. The
quartic positivity arguments cover the entire nonnegative real half-axis.
-/
namespace SPR.DegreeNecessity
noncomputable section
open N6

/-- Quartic remaining after the contact square in corner 0. -/
def F0 (t : ℝ) : ℝ :=
  (9/250) * t^0 + (2325246801607113/10208966953631500) * t^1 + (57094101348581227/10208966953631500) * t^2 + (-1252042944999614/2552241738407875) * t^3 + (1/25) * t^4

/-- Quartic remaining after the contact square in corner 1. -/
def F1 (t : ℝ) : ℝ :=
  (90) * t^0 + (53727500481470645241/10208966953631500) * t^1 + (126021414955216817453/10208966953631500) * t^2 + (-101810367438269889/2552241738407875) * t^3 + (1/25) * t^4

/-- Quartic remaining after the contact square in corner 2. -/
def F2 (t : ℝ) : ℝ :=
  (55080) * t^0 + (23406302273232975276/102089669536315) * t^1 + (102966285353162075756/2552241738407875) * t^2 + (-16450028191179889/204179339072630) * t^3 + (1/25) * t^4

/-- Quartic remaining after the contact square in corner 3. -/
def F3 (t : ℝ) : ℝ :=
  (6120) * t^0 + (4604582188848296296/20417933907263) * t^1 + (2700257383808100617/204179339072630) * t^2 + (-42271826365478491/1020896695363150) * t^3 + (1/25) * t^4

theorem square0 (t : ℝ) :
    numeratorEven witness t * E₀ t + t * numeratorOdd witness t * O₀ t =
      (t - 1000)^2 * F0 t := by
  dsimp [numeratorEven, numeratorOdd, witness]
  norm_num [E₀, O₀, F0]
  <;> ring

theorem square1 (t : ℝ) :
    numeratorEven witness t * E₀ t + t * numeratorOdd witness t * O₁ t =
      (t - 20)^2 * F1 t := by
  dsimp [numeratorEven, numeratorOdd, witness]
  norm_num [E₀, O₁, F1]
  <;> ring

theorem square2 (t : ℝ) :
    numeratorEven witness t * E₁ t + t * numeratorOdd witness t * O₀ t =
      (t - 1)^2 * F2 t := by
  dsimp [numeratorEven, numeratorOdd, witness]
  norm_num [E₁, O₀, F2]
  <;> ring

theorem square3 (t : ℝ) :
    numeratorEven witness t * E₁ t + t * numeratorOdd witness t * O₁ t =
      (t - 3)^2 * F3 t := by
  dsimp [numeratorEven, numeratorOdd, witness]
  norm_num [E₁, O₁, F3]
  <;> ring

/-- A positive quadratic times a square, plus nonnegative lower terms. -/
theorem quartic_pos {a b c d e t : ℝ} (ha : 0 < a) (he : 0 < e)
    (hd : 0 ≤ d) (hdisc : b^2 < 4*a*c) (ht : 0 ≤ t) :
    0 < a*t^4+b*t^3+c*t^2+d*t+e := by
  have hq : 0 < a*t^2+b*t+c := by
    nlinarith [sq_nonneg (2*a*t+b)]
  have hm := mul_nonneg (sq_nonneg t) hq.le
  have hn := mul_nonneg hd ht
  nlinarith

theorem F0_pos {t : ℝ} (ht : 0 ≤ t) : 0 < F0 t := by
  have h := quartic_pos (a := (1/25)) (b := (-1252042944999614/2552241738407875))
    (c := (57094101348581227/10208966953631500)) (d := (2325246801607113/10208966953631500)) (e := (9/250))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ht
  dsimp [F0]
  nlinarith only [h]

theorem F1_pos {t : ℝ} (ht : 0 ≤ t) : 0 < F1 t := by
  have h := quartic_pos (a := (1/25)) (b := (-101810367438269889/2552241738407875))
    (c := (126021414955216817453/10208966953631500)) (d := (53727500481470645241/10208966953631500)) (e := (90))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ht
  dsimp [F1]
  nlinarith only [h]

theorem F3_pos {t : ℝ} (ht : 0 ≤ t) : 0 < F3 t := by
  have h := quartic_pos (a := (1/25)) (b := (-42271826365478491/1020896695363150))
    (c := (2700257383808100617/204179339072630)) (d := (4604582188848296296/20417933907263)) (e := (6120))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ht
  dsimp [F3]
  nlinarith only [h]

/-- The exceptional quartic uses a square centred at 1010 and two intervals. -/
theorem F2_pos {t : ℝ} (ht : 0 ≤ t) : 0 < F2 t := by
  let L : ℝ := -16450028191179889/204179339072630 + 2*1010/25
  let Z₂ : ℝ := 102966285353162075756/2552241738407875 - 1010^2/25 + 2*1010*L
  let Z₁ : ℝ := 23406302273232975276/102089669536315 - 1010^2*L
  have hL : 0 < L := by norm_num [L]
  have hZ : 0 < Z₂ := by norm_num [Z₂, L]
  have hT : 0 < (2440/3)*Z₂+Z₁ := by norm_num [Z₂, Z₁, L]
  have hR : 0 < L*(1010-2440/3)^2+Z₁ := by norm_num [Z₁, L]
  have hid : F2 t = (t-1010)^2*(t^2/25+L*t)+Z₂*t^2+Z₁*t+55080 := by
    dsimp [F2, Z₂, Z₁, L]
    ring
  rw [hid]
  by_cases h : 2440/3 ≤ t
  · have hz : 0 ≤ Z₂*t+Z₁ := by
      exact hT.le.trans (by
        simpa only [mul_comm Z₂ (2440/3), add_comm Z₁] using
          add_le_add_right (mul_le_mul_of_nonneg_left h hZ.le) Z₁)
    have hm := mul_nonneg ht hz
    have hs := mul_nonneg (sq_nonneg (t-1010))
      (add_nonneg (div_nonneg (sq_nonneg t) (by norm_num : (0:ℝ) ≤ 25)) (mul_nonneg hL.le ht))
    dsimp [Z₂, Z₁, L] at hm hs ⊢
    nlinarith only [hm, hs]
  · have hs : (1010-2440/3)^2 ≤ (t-1010)^2 := by nlinarith
    have hlin : 0 ≤ L*(t-1010)^2+Z₁ := by
      apply hR.le.trans
      exact add_le_add (mul_le_mul_of_nonneg_left hs hL.le) le_rfl
    have hm := mul_nonneg ht hlin
    have hq := mul_nonneg (sq_nonneg (t-1010)) (sq_nonneg t)
    have hz := mul_nonneg hZ.le (sq_nonneg t)
    dsimp [Z₂, Z₁, L] at hm hz ⊢
    nlinarith only [hm, hq, hz]

end
end SPR.DegreeNecessity
