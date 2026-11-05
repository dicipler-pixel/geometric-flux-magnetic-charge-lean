import MonopoleStance.Geometry
import Mathlib.Analysis.SpecificLimits.Basic

/-! An actual analytic obstruction on the axis of the normalized Pauli family.
This is a parameter-space gap-defect statement, not an EM source equation. -/
namespace MonopoleStance
open Filter Topology

/-- A real-valued coordinate with different constant one-sided values cannot
be continuously extended to the meeting point. -/
theorem no_continuous_jump_extension (f : ℝ → ℝ)
    (hp : ∀ t, 0 < t → f t = 0) (hn : ∀ t, t < 0 → f t = 1) :
    ¬ ContinuousAt f 0 := by
  intro hf
  have hz := hf.tendsto.comp tendsto_one_div_add_atTop_nhds_zero_nat
  have hpos : (fun n : ℕ => f (1 / ((n:ℝ) + 1))) = (fun _ => 0) := by
    funext n
    exact hp _ (by positivity)
  simp only [Function.comp_def] at hz
  rw [hpos] at hz
  have eq0 : f 0 = 0 := tendsto_nhds_unique hz tendsto_const_nhds
  have hlim : Tendsto (fun n : ℕ => -(1 / ((n:ℝ) + 1))) atTop (𝓝 0) := by
    simpa using tendsto_one_div_add_atTop_nhds_zero_nat.neg
  have ho := hf.tendsto.comp hlim
  have hneg : (fun n : ℕ => f (-(1 / ((n:ℝ) + 1)))) = (fun _ => 1) := by
    funext n
    apply hn
    have hh : (0:ℝ) < 1 / ((n:ℝ) + 1) := by positivity
    linarith
  simp only [Function.comp_def] at ho
  rw [hneg] at ho
  have eq1 : f 0 = 1 := tendsto_nhds_unique ho tendsto_const_nhds
  linarith

/-- On the positive and negative z-axis the lower eigenprojectors of d·σ
are distinct constants. No continuous matrix-valued extension at d=0 can
agree with both axis restrictions. The hypotheses specify those restrictions;
the three-dimensional radial family and eigenvalue-gap theorem are not built here. -/
theorem no_continuous_Pauli_axis_extension
    (F : ℝ → Matrix (Fin 2) (Fin 2) ℂ)
    (hp : ∀ t, 0 < t → F t = lowerProjector 0 0 1)
    (hn : ∀ t, t < 0 → F t = lowerProjector 0 0 (-1)) :
    ¬ ContinuousAt F 0 := by
  intro hF
  have hc : ContinuousAt (fun t => (F t 0 0).re) 0 := by
    exact Complex.continuous_re.continuousAt.comp
      ((continuous_apply 0).continuousAt.comp
        ((continuous_apply 0).continuousAt.comp hF))
  apply no_continuous_jump_extension (fun t => (F t 0 0).re) ?_ ?_ hc
  · intro t ht
    simp [hp t ht, lowerProjector]
  · intro t ht
    simp [hn t ht, lowerProjector]

end MonopoleStance
