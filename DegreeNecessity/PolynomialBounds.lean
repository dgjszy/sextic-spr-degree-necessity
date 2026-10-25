import DegreeNecessity.Basic
import SPR.Segment.RationalStrict

/-!
# Polynomial bridges for the lower-degree obstruction

The candidate is an arbitrary real polynomial of degree at most five. These
lemmas recover its six coefficients and the necessary highest pairing coefficient.
-/
namespace SPR.DegreeNecessity
noncomputable section
open Polynomial N6 Filter
open scoped Topology

/-- Nonnegativity on a half-axis forces a nonnegative top allowed coefficient. -/
theorem top_coefficient_nonneg {p : ℝ[X]} {n : ℕ} (hn : 0 < n)
    (hd : p.natDegree ≤ n) (hp : ∀ x : ℝ, 0 ≤ x → 0 ≤ p.eval x) :
    0 ≤ p.coeff n := by
  by_contra h
  have hc : p.coeff n < 0 := lt_of_not_ge h
  have hdeg : p.natDegree = n := le_antisymm hd (le_natDegree_of_ne_zero hc.ne)
  have hlc : p.leadingCoeff < 0 := by rwa [← coeff_natDegree, hdeg]
  have ht := p.tendsto_atBot_of_leadingCoeff_nonpos
    (natDegree_pos_iff_degree_pos.mp (by omega)) hlc.le
  obtain ⟨x,hx,hpx⟩ := ((eventually_ge_atTop (0:ℝ)).and
    (ht.eventually (eventually_lt_atBot (0:ℝ)))).exists
  exact (not_lt_of_ge (hp x hx)) hpx

/-- Descending coordinates for an arbitrary polynomial of degree at most five. -/
def lowVector (p : ℝ[X]) : Vec7 :=
  ![0, p.coeff 5, p.coeff 4, p.coeff 3, p.coeff 2, p.coeff 1, p.coeff 0]

/-- The coordinates represent the entire degree-at-most-five polynomial space. -/
theorem lowVector_poly {p : ℝ[X]} (hp : p.natDegree ≤ 5) :
    numeratorPoly (lowVector p) = p := by
  ext n
  by_cases hn : n ≤ 6
  · interval_cases n <;>
      simp [numeratorPoly, lowVector, Matrix.cons_val_succ, coeff_add,
        coeff_C_mul_X_pow, coeff_C_mul_X,
        coeff_eq_zero_of_natDegree_lt (show p.natDegree < 6 by omega)]
  · have hn' : p.natDegree < n := by omega
    simp [numeratorPoly, lowVector, Matrix.cons_val_succ, coeff_add,
      coeff_C_mul_X_pow, coeff_C_mul_X, coeff_X, coeff_C, coeff_eq_zero_of_natDegree_lt hn',
      show n ≠ 0 by omega, show n ≠ 1 by omega, show 1 ≠ n by omega, show n ≠ 2 by omega,
      show n ≠ 3 by omega, show n ≠ 4 by omega, show n ≠ 5 by omega]

/-- The cleared pairing polynomial for a candidate with zero sextic coefficient. -/
def lowPairPoly (a : Poly6) (b : Vec7) : ℝ[X] :=
  C (b 6*a.a6) + C (-b 4*a.a6-b 6*a.a4+b 5*a.a5)*X +
  C (b 2*a.a6+b 4*a.a4+b 6*a.a2-b 3*a.a5-b 5*a.a3)*X^2 +
  C (-b 2*a.a4-b 4*a.a2-b 6+b 1*a.a5+b 3*a.a3+b 5*a.a1)*X^3 +
  C (b 2*a.a2+b 4-b 1*a.a3-b 3*a.a1)*X^4 + C (a.a1*b 1-b 2)*X^5

theorem lowPair_eval (a : Poly6) (b : Vec7) (h : b 0 = 0) (t : ℝ) :
    (lowPairPoly a b).eval t = pairing a b t := by
  simp [lowPairPoly, pairing, numeratorEven, numeratorOdd, evenPart, oddPart, h]
  ring

/-- The frequency condition supplies the necessary inequality at infinity. -/
theorem tail_nonneg {a : Poly6} {b : Vec7} (h : b 0 = 0)
    (hp : ∀ t : ℝ, 0 ≤ t → 0 ≤ pairing a b t) : 0 ≤ a.a1*b 1-b 2 := by
  have hc := top_coefficient_nonneg (p := lowPairPoly a b) (n := 5) (by omega)
    (by unfold lowPairPoly; compute_degree!)
    (by intro t ht; rw [lowPair_eval a b h]; exact hp t ht)
  simpa only [lowPairPoly, coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X, coeff_C,
    show (5:ℕ) ≠ 0 by omega, show (5:ℕ) ≠ 1 by omega,
    show (5:ℕ) ≠ 2 by omega, show (5:ℕ) ≠ 3 by omega, show (5:ℕ) ≠ 4 by omega,
    if_false, if_true, add_zero, zero_add] using hc

/-- Boundary positive-realness forces the highest allowed numerator coefficient nonnegative. -/
theorem fifth_coefficient_nonneg_weak {a : Poly6} (ha : SPR.IsHurwitz a.toPoly)
    {p : ℝ[X]} (hp0 : p ≠ 0) (hd : p.natDegree ≤ 5)
    (hs : ∀ ω : ℝ, 0 ≤ (eval (Complex.I*(ω:ℂ)) (p.map (algebraMap ℝ ℂ)) /
      eval (Complex.I*(ω:ℂ)) (a.toPoly.map (algebraMap ℝ ℂ))).re) :
    0 ≤ p.coeff 5 := by
  have ev (q : ℝ[X]) (y : ℝ) :
      q.eval₂ (algebraMap ℝ ℂ) (y:ℂ) = Complex.ofReal (q.eval y) :=
    Polynomial.aeval_ofReal (K := ℂ) q y
  apply top_coefficient_nonneg (by omega : 0 < 5) hd
  intro x hx
  by_cases hz : x = 0
  · subst x
    have h := hs 0
    have ha0 := SPR.Hurwitz.eval_pos ha (by rw [(sextic_monic a).leadingCoeff]; norm_num)
      (x := 0) (by norm_num)
    have hh : (0:ℝ) ≤ p.eval 0 / a.toPoly.eval 0 := by
      simp only [Complex.ofReal_zero, mul_zero, eval_map] at h
      change 0 ≤ (p.eval₂ (algebraMap ℝ ℂ) (0:ℂ) /
        a.toPoly.eval₂ (algebraMap ℝ ℂ) (0:ℂ)).re at h
      have ev0 (q : ℝ[X]) := ev q 0
      simp only [Complex.ofReal_zero] at ev0
      rwa [ev0 p, ev0 a.toPoly, ← Complex.ofReal_div, Complex.ofReal_re] at h
    simpa only [zero_mul] using (le_div_iff₀ ha0).mp hh
  · have hx' : 0 < x := lt_of_le_of_ne hx (Ne.symm hz)
    have h := SPR.Segment.weak_ratio_strict_interior ha hp0
      (by rw [sextic_natDegree]; omega)
      (by intro ω; simpa [SPR.Segment.value, eval_map] using hs ω)
      (z := (x:ℂ)) hx'
    change 0 < (p.eval₂ (algebraMap ℝ ℂ) (x:ℂ) /
      a.toPoly.eval₂ (algebraMap ℝ ℂ) (x:ℂ)).re at h
    rw [ev p x, ev a.toPoly x,
      ← Complex.ofReal_div, Complex.ofReal_re] at h
    exact ((div_pos_iff_of_pos_right
      (SPR.Hurwitz.eval_pos ha (by rw [(sextic_monic a).leadingCoeff]; norm_num) hx)).mp h).le

/-- Strict frequency positivity implies the same necessary coefficient inequality. -/
theorem fifth_coefficient_nonneg {a : Poly6} (ha : SPR.IsHurwitz a.toPoly)
    {p : ℝ[X]} (hd : p.natDegree ≤ 5) (hs : FrequencySPR a.toPoly p) :
    0 ≤ p.coeff 5 := by
  apply fifth_coefficient_nonneg_weak ha _ hd (fun ω => (hs ω).le)
  intro hz
  have h := hs 0
  simp [hz] at h

end
end SPR.DegreeNecessity
