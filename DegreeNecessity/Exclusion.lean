import DegreeNecessity.Stability
import DegreeNecessity.PolynomialBounds

/-!
# Exclusion of every numerator of degree at most five

Four actual corner/frequency inequalities and the leading pairing coefficient
have a positive rational combination equal to -A b(0)-B coeff(b,5).
-/
namespace SPR.DegreeNecessity
noncomputable section
open Polynomial N6

/-- Positive multiplier of finite-frequency inequality 0. -/
def w0 : ℝ :=
  8256045670735893686284547369288025947743339610759980000000000000 /
  8126841400921594268030245759113023979161854092290728754012518759740951801021

theorem w0_pos : 0 < w0 := by norm_num [w0]

/-- Positive multiplier of finite-frequency inequality 1. -/
def w1 : ℝ :=
  207370529783676202655902573561734143170386069680000000000000000000 /
  2717087538764161512963840051219767315911512428806190068201845916153288007

theorem w1_pos : 0 < w1 := by norm_num [w1]

/-- Positive multiplier of finite-frequency inequality 2. -/
def w2 : ℝ :=
  2673385325732820685221322348208524307045425221010000000000000000000000 /
  8151262616292484538891520153659301947734537286418570204605537748459864021

theorem w2_pos : 0 < w2 := by norm_num [w2]

/-- Positive multiplier of finite-frequency inequality 3. -/
def w3 : ℝ :=
  1228721022841881408898278851283260151083273871319430000000000000000000000 /
  24380524202764782804090737277339071937485562276872186262037556279222855403063

theorem w3_pos : 0 < w3 := by norm_num [w3]

/-- Positive residual coefficient in the separating identity. -/
def A : ℝ :=
  23046797004185631819643050257180682267915284584118958515075399780915999747000 /
  24404904726967547586894828014616411009423047839149058448299593835502078258466063

theorem A_pos : 0 < A := by norm_num [A]

/-- Positive residual coefficient in the separating identity. -/
def B : ℝ :=
  495887497130760051770684011992448726017627549119721795277556599868183122181 /
  16286238993591377700082957349968635260208865707130010398812263233686042000000000

theorem B_pos : 0 < B := by norm_num [B]

/-- The four rows evaluate the actual contracted box, not its auxiliary boundary. -/
def f₀ (b : Vec7) := pairing (box.corner (false,false)) b 999
def f₁ (b : Vec7) := pairing (box.corner (false,true)) b (1001/50)
def f₂ (b : Vec7) := pairing (box.corner (true,false)) b (1001/1000)
def f₃ (b : Vec7) := pairing (box.corner (true,true)) b (2997/1000)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
/-- Exact finite separation identity on the entire six-dimensional coefficient space.
The larger local budget accommodates the exact rational multipliers. -/
theorem separation_identity (b : Vec7) (hb : b 0 = 0) :
    (lower.a1*b 1-b 2) + w0*f₀ b + w1*f₁ b + w2*f₂ b + w3*f₃ b =
      -A*b 6-B*b 1 := by
  norm_num [f₀,f₁,f₂,f₃,pairing,numeratorEven,numeratorOdd,evenPart,oddPart,
    box,lower,upper,Box6.corner,hb,w0,w1,w2,w3,A,B]
  <;> ring

/-- No real polynomial of degree at most five is a common strict numerator. -/
theorem no_lower_degree : ¬ ∃ p : ℝ[X], p.natDegree ≤ 5 ∧
    ∀ a : Poly6, box.Contains a → FrequencySPR a.toPoly p := by
  rintro ⟨p,hd,hp⟩
  let b := lowVector p
  have hb : b 0 = 0 := rfl
  have hrepr : numeratorPoly b = p := lowVector_poly hd
  have hpair (a : Poly6) (ha : box.Contains a) (t : ℝ) (ht : 0 ≤ t) :
      0 < pairing a b t := by
    apply (frequencySPR_iff (robustly_hurwitz a ha) b).mp
    · rw [hrepr]
      exact hp a ha
    · exact ht
  have h0 := hpair box.lower box.lower_mem 0 (by norm_num)
  have hc : 0 < b 6 := by
    have ha : 0 < box.lower.a6 := by norm_num [box,lower]
    have hp0 : 0 < b 6 * box.lower.a6 := by
      simpa [pairing,numeratorEven,numeratorOdd,evenPart,oddPart] using h0
    exact (mul_pos_iff_of_pos_right ha).mp hp0
  have hc5 : 0 ≤ b 1 := fifth_coefficient_nonneg
    (robustly_hurwitz box.lower box.lower_mem) hd (hp box.lower box.lower_mem)
  have ht := tail_nonneg hb (fun t ht => (hpair (box.corner (false,false))
    (box.corner_mem _) t ht).le)
  change 0 ≤ lower.a1*b 1-b 2 at ht
  have h₀ : 0 ≤ f₀ b := (hpair _ (box.corner_mem _) _ (by norm_num)).le
  have h₁ : 0 ≤ f₁ b := (hpair _ (box.corner_mem _) _ (by norm_num)).le
  have h₂ : 0 ≤ f₂ b := (hpair _ (box.corner_mem _) _ (by norm_num)).le
  have h₃ : 0 ≤ f₃ b := (hpair _ (box.corner_mem _) _ (by norm_num)).le
  have hs := separation_identity b hb
  have hn := add_nonneg (add_nonneg (add_nonneg (add_nonneg ht
    (mul_nonneg w0_pos.le h₀)) (mul_nonneg w1_pos.le h₁))
    (mul_nonneg w2_pos.le h₂)) (mul_nonneg w3_pos.le h₃)
  rw [hs] at hn
  have hA := mul_pos A_pos hc
  have hB := mul_nonneg B_pos.le hc5
  linarith

/-- One fixed numerator has nonnegative real quotient on the entire box and axis. -/
def CommonWeak (p : ℝ[X]) : Prop :=
  ∀ a : Poly6, box.Contains a → ∀ ω : ℝ,
    0 ≤ (eval (Complex.I*(ω:ℂ)) (p.map (algebraMap ℝ ℂ)) /
      eval (Complex.I*(ω:ℂ)) (a.toPoly.map (algebraMap ℝ ℂ))).re

set_option maxHeartbeats 800000 in
/-- Even weak positive-realness is impossible for a nonzero lower-degree numerator.
The local budget covers rational elimination in the four finite rows. -/
theorem no_nonzero_weak : ¬ ∃ p : ℝ[X], p ≠ 0 ∧ p.natDegree ≤ 5 ∧ CommonWeak p := by
  rintro ⟨p,hp0,hd,hp⟩
  let b := lowVector p
  have hb : b 0 = 0 := rfl
  have hrepr : numeratorPoly b = p := lowVector_poly hd
  have hpair (a : Poly6) (ha : box.Contains a) (t : ℝ) (ht : 0 ≤ t) :
      0 ≤ pairing a b t := by
    have hw := hp a ha (Real.sqrt t)
    rw [← hrepr] at hw
    change 0 ≤ (eval (Complex.I*(Real.sqrt t:ℂ))
      ((numeratorPoly b).map (algebraMap ℝ ℂ)) / frequencyValue a (Real.sqrt t)).re at hw
    rw [real_ratio_eq, Real.sq_sqrt ht] at hw
    simpa only [zero_mul] using (le_div_iff₀ (Complex.normSq_pos.mpr
      (hurwitz_frequencyValue_ne_zero (robustly_hurwitz a ha) _))).mp hw
  have h0 := hpair box.lower box.lower_mem 0 (by norm_num)
  have hc : 0 ≤ b 6 := by
    have ha : 0 < box.lower.a6 := by norm_num [box,lower]
    have h : 0 ≤ b 6 * box.lower.a6 := by
      simpa [pairing,numeratorEven,numeratorOdd,evenPart,oddPart] using h0
    exact (mul_nonneg_iff_of_pos_right ha).mp h
  have hc5 : 0 ≤ b 1 := fifth_coefficient_nonneg_weak
    (robustly_hurwitz box.lower box.lower_mem) hp0 hd (hp box.lower box.lower_mem)
  have ht := tail_nonneg hb (hpair (box.corner (false,false)) (box.corner_mem _))
  change 0 ≤ lower.a1*b 1-b 2 at ht
  have h₀ : 0 ≤ f₀ b := hpair _ (box.corner_mem _) _ (by norm_num)
  have h₁ : 0 ≤ f₁ b := hpair _ (box.corner_mem _) _ (by norm_num)
  have h₂ : 0 ≤ f₂ b := hpair _ (box.corner_mem _) _ (by norm_num)
  have h₃ : 0 ≤ f₃ b := hpair _ (box.corner_mem _) _ (by norm_num)
  have hw0 := mul_nonneg w0_pos.le h₀
  have hw1 := mul_nonneg w1_pos.le h₁
  have hw2 := mul_nonneg w2_pos.le h₂
  have hw3 := mul_nonneg w3_pos.le h₃
  have hs := separation_identity b hb
  have hn := add_nonneg (add_nonneg (add_nonneg (add_nonneg ht hw0) hw1) hw2) hw3
  rw [hs] at hn
  have hA := mul_nonneg A_pos.le hc
  have hB := mul_nonneg B_pos.le hc5
  have hz6 : b 6 = 0 := le_antisymm
    (le_of_not_gt (fun h => (not_le_of_gt (mul_pos A_pos h))
      (by linarith only [hn,hB]))) hc
  have hz1 : b 1 = 0 := le_antisymm
    (le_of_not_gt (fun h => (not_le_of_gt (mul_pos B_pos h))
      (by linarith only [hn,hA]))) hc5
  rw [hz6,hz1] at hs
  rw [hz1] at ht
  simp only [mul_zero,sub_zero,zero_sub] at hs ht
  have he0 : w0*f₀ b = 0 := by linarith only [hs,ht,hw0,hw1,hw2,hw3]
  have he1 : w1*f₁ b = 0 := by linarith only [hs,ht,hw0,hw1,hw2,hw3]
  have he2 : w2*f₂ b = 0 := by linarith only [hs,ht,hw0,hw1,hw2,hw3]
  have he3 : w3*f₃ b = 0 := by linarith only [hs,ht,hw0,hw1,hw2,hw3]
  have hf0 := (mul_eq_zero.mp he0).resolve_left w0_pos.ne'
  have hf1 := (mul_eq_zero.mp he1).resolve_left w1_pos.ne'
  have hf2 := (mul_eq_zero.mp he2).resolve_left w2_pos.ne'
  have hf3 := (mul_eq_zero.mp he3).resolve_left w3_pos.ne'
  norm_num [f₀,f₁,f₂,f₃,pairing,numeratorEven,numeratorOdd,evenPart,oddPart,
    box,lower,upper,Box6.corner,hb,hz6,hz1] at hf0 hf1 hf2 hf3
  have hz2 : b 2 = 0 := by linarith only [hf0,hf1,hf2,hf3]
  have hz3 : b 3 = 0 := by linarith only [hf0,hf1,hf2,hf3]
  have hz4 : b 4 = 0 := by linarith only [hf0,hf1,hf2,hf3]
  have hz5 : b 5 = 0 := by linarith only [hf0,hf1,hf2,hf3]
  apply hp0
  rw [← hrepr]
  simp [numeratorPoly,hb,hz1,hz2,hz3,hz4,hz5,hz6]

end
end SPR.DegreeNecessity
