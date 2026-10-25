import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Order.Compact

/-!
# Boundedness on a closed domain from decay at infinity

Outside a bounded exceptional set the function has norm at most one. Compactness
of the exceptional closure gives one bound on the remaining part of the domain.
-/

namespace SPR.Segment.Analysis

open Set Filter Bornology
open scoped Topology

/-- A function continuous on a closed subset of a proper space and tending to zero
at infinity is bounded on that subset, even if it has poles outside the subset. -/
theorem bounded_on_closed_of_tendsto {α E : Type*}
    [PseudoMetricSpace α] [ProperSpace α] [NormedAddCommGroup E]
    {s : Set α} (hs : IsClosed s) {F : α → E} (hF : ContinuousOn F s)
    (hlim : Tendsto F (cobounded α) (𝓝 0)) :
    ∃ M : ℝ, ∀ x ∈ s, ‖F x‖ ≤ M := by
  have he : ∀ᶠ x in cobounded α, ‖F x‖ ≤ 1 :=
    (hlim.norm.eventually (gt_mem_nhds (by simp : ‖(0 : E)‖ < (1 : ℝ)))).mono
      (fun _ h => h.le)
  let bad := {x : α | ¬‖F x‖ ≤ 1}
  have hb : IsBounded bad := by
    change ∀ᶠ x in cobounded α, x ∉ bad
    filter_upwards [he] with x hx
    exact fun hbad => hbad hx
  have hc : IsCompact (closure bad ∩ s) := hb.isCompact_closure.inter_right hs
  obtain ⟨C, hC⟩ := hc.exists_bound_of_continuousOn (hF.mono inter_subset_right)
  refine ⟨max C 1, ?_⟩
  intro x hx
  by_cases hg : ‖F x‖ ≤ 1
  · exact hg.trans (le_max_right _ _)
  · exact (hC x ⟨subset_closure hg, hx⟩).trans (le_max_left _ _)

end SPR.Segment.Analysis
