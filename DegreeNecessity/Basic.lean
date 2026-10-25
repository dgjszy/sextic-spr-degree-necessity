import SPR.N6.Definitions.Box

/-!
# A full-width sextic interval box requiring a sextic numerator

The endpoints are the auxiliary box contracted about its centre by
999999999/1000000000. Coefficients in `Poly6` are in descending order.
-/
namespace SPR.DegreeNecessity
noncomputable section
open Polynomial N6

/-- The six actual lower coefficient endpoints. -/
def lower : Poly6 :=
  ⟨2000000039/2000000000, 20402000000039/20000000000,
   1840000000081/2000000000, 8166000016019/2000000000,
   10000000007/10000000, 200000000053/100000000⟩

/-- The six actual upper coefficient endpoints. -/
def upper : Poly6 :=
  ⟨79999999961/2000000000, 20479999999961/20000000000,
   2001999999919/2000000000, 40203999983981/2000000000,
   23999999993/10000000, 305999999947/100000000⟩

/-- The explicit independent closed coefficient box. -/
def box : Box6 where
  lower := lower
  upper := upper
  h1 := by norm_num [lower, upper]
  h2 := by norm_num [lower, upper]
  h3 := by norm_num [lower, upper]
  h4 := by norm_num [lower, upper]
  h5 := by norm_num [lower, upper]
  h6 := by norm_num [lower, upper]

/-- Every coefficient interval has strictly positive width. -/
theorem full_width :
    lower.a1 < upper.a1 ∧ lower.a2 < upper.a2 ∧ lower.a3 < upper.a3 ∧
    lower.a4 < upper.a4 ∧ lower.a5 < upper.a5 ∧ lower.a6 < upper.a6 := by
  norm_num [lower, upper]

/-- The even auxiliary lower endpoint. -/
def E₀ (t : ℝ) := -(t-1/10)*(t-20)*(t-1000)
/-- The even auxiliary upper endpoint. -/
def E₁ (t : ℝ) := -(t-1)*(t-3)*(t-1020)
/-- The odd auxiliary lower endpoint. -/
def O₀ (t : ℝ) := (t-1)*(t-1000)
/-- The odd auxiliary upper endpoint. -/
def O₁ (t : ℝ) := 40*(t-3)*(t-20)

/-- The fixed explicit sextic numerator, in descending coefficient order. -/
def witness : Vec7 := ![1/25, 1, 41536780744817023/1020896695363150,
  3548520832221173603/5104483476815750, 382280686567850379/1020896695363150,
  6832048626988833273/5104483476815750, 18]

/-- The numerator has actual degree six. -/
theorem witness_degree : (numeratorPoly witness).natDegree = 6 :=
  numeratorPoly_degree witness (by norm_num [witness])

end
end SPR.DegreeNecessity
