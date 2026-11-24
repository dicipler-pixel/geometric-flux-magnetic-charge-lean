import Mathlib

open Filter Topology
open scoped Topology

set_option maxHeartbeats 1000000

noncomputable section

namespace PeelWall

/-- The overlap of two unit eigenvectors of a two-dimensional rank-one spectral
projector, expressed through the projector's squared Frobenius norm. -/
def overlapFromNormSq (F : ℝ) : ℝ := Real.sqrt (1 - F⁻¹)

theorem tendsto_inv_normSq {F : ℝ → ℝ}
    (hF : Tendsto (fun d => d * F d) (nhdsWithin 0 (Set.Ioi 0)) (nhds (1 / 2))) :
    Tendsto (fun d => (F d)⁻¹) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  let l := nhdsWithin (0 : ℝ) (Set.Ioi 0)
  have hd : Tendsto (fun d : ℝ => d) l (nhds 0) :=
    Filter.tendsto_id.mono_left nhdsWithin_le_nhds
  have hpos : ∀ᶠ d in l, 0 < d * F d :=
    hF.eventually (Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  have heq : (fun d => (F d)⁻¹) =ᶠ[l] (fun d => d / (d * F d)) := by
    filter_upwards [hpos] with d hdF
    have hne : d ≠ 0 ∧ F d ≠ 0 := mul_ne_zero_iff.mp (ne_of_gt hdF)
    field_simp [hne.1, hne.2]
  have hlim : Tendsto (fun d => d / (d * F d)) l (nhds 0) := by
    convert hd.div hF (by norm_num : (1 / 2 : ℝ) ≠ 0) using 1 <;> norm_num
  exact hlim.congr' heq.symm

theorem overlapFromNormSq_tendsto {F : ℝ → ℝ}
    (hF : Tendsto (fun d => d * F d) (nhdsWithin 0 (Set.Ioi 0)) (nhds (1 / 2))) :
    Tendsto (fun d => overlapFromNormSq (F d))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
  have hi := tendsto_inv_normSq hF
  have hs : Tendsto (fun d => 1 - (F d)⁻¹)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
    simpa using hi.const_sub 1
  have hsqrt := (Real.continuous_sqrt.tendsto 1).comp hs
  unfold overlapFromNormSq
  change Tendsto ((fun x : ℝ => Real.sqrt x) ∘ fun d => 1 - (F d)⁻¹)
    (nhdsWithin 0 (Set.Ioi 0)) (nhds 1)
  simpa using hsqrt

end PeelWall

namespace PeelWall

/-- The condition-number limit follows from the squared projector-norm limit and
its unsquared form.  Here `overlapFromNormSq (F d)` is the exact overlap when
`F d` is the squared Frobenius norm of a rank-one spectral projector. -/
theorem kappa_limit_of_projector_norm {F : ℝ → ℝ}
    (hF : Tendsto (fun d => d * F d) (nhdsWithin 0 (Set.Ioi 0)) (nhds (1 / 2)))
    (hNorm : Tendsto (fun d => Real.sqrt d * Real.sqrt (F d))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (1 / Real.sqrt 2))) :
    Tendsto
      (fun d => Real.sqrt d * ((1 + overlapFromNormSq (F d)) * Real.sqrt (F d)))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (Real.sqrt 2)) := by
  have hc := overlapFromNormSq_tendsto hF
  have hfac : Tendsto (fun d => 1 + overlapFromNormSq (F d))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (1 + 1)) :=
    tendsto_const_nhds.add hc
  have hprod := hfac.mul hNorm
  have hs : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  have hval : (1 + 1) * (1 / Real.sqrt 2) = Real.sqrt 2 := by
    field_simp [hs]
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  rw [← hval]
  convert hprod using 1
  funext d
  ring

/-- The real identity underlying `(1 + c) * ‖P‖_F = κ`. -/
theorem overlap_identity {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1) :
    (1 + c) / Real.sqrt (1 - c^2) = Real.sqrt ((1 + c) / (1 - c)) := by
  have hp : 0 < 1 + c := by linarith
  have hm : 0 < 1 - c := by linarith
  have hprod : 0 < 1 - c^2 := by
    nlinarith [mul_pos hp hm]
  symm
  rw [Real.sqrt_eq_iff_mul_self_eq (by positivity) (by positivity)]
  rw [div_mul_div_comm, Real.mul_self_sqrt hprod.le]
  field_simp [ne_of_gt hm, ne_of_gt hprod]
  <;> ring


theorem overlapFromNormSq_sq {F : ℝ} (hF : 1 ≤ F) :
    (overlapFromNormSq F)^2 = 1 - F⁻¹ := by
  rw [overlapFromNormSq, Real.sq_sqrt]
  exact sub_nonneg.2 (inv_le_one_of_one_le₀ hF)

theorem overlapFromNormSq_lt_one {F : ℝ} (hF : 1 ≤ F) :
    overlapFromNormSq F < 1 := by
  have hFpos : 0 < F := by linarith
  have hinv : 0 < F⁻¹ := inv_pos.2 hFpos
  have hsq := overlapFromNormSq_sq hF
  have hc0 := Real.sqrt_nonneg (1 - F⁻¹)
  unfold overlapFromNormSq at hsq ⊢
  nlinarith [sq_nonneg (Real.sqrt (1 - F⁻¹) - 1)]

/-- The exact Frobenius/overlap factor identity, including the endpoint F = 1. -/
theorem overlapFromNormSq_condition_identity {F : ℝ} (hF : 1 ≤ F) :
    (1 + overlapFromNormSq F) * Real.sqrt F =
      Real.sqrt ((1 + overlapFromNormSq F) / (1 - overlapFromNormSq F)) := by
  have hsq := overlapFromNormSq_sq hF
  have hc0 : 0 ≤ overlapFromNormSq F := Real.sqrt_nonneg _
  have hc1 := overlapFromNormSq_lt_one hF
  calc
    (1 + overlapFromNormSq F) * Real.sqrt F =
        (1 + overlapFromNormSq F) / Real.sqrt (1 - (overlapFromNormSq F)^2) := by
      rw [hsq, sub_sub_cancel, Real.sqrt_inv, div_eq_mul_inv, inv_inv]
    _ = Real.sqrt ((1 + overlapFromNormSq F) / (1 - overlapFromNormSq F)) :=
      overlap_identity hc0 hc1

end PeelWall

namespace PeelWall

open scoped Matrix BigOperators Complex
open Complex

/-- Sum of the squared moduli of the four entries. -/
def entryNormSq (M : Matrix (Fin 2) (Fin 2) ℂ) : ℝ :=
  ∑ i, ∑ j, Complex.normSq (M i j)

theorem entryNormSq_real_smul (r : ℝ) (M : Matrix (Fin 2) (Fin 2) ℂ) :
    entryNormSq ((r : ℂ) • M) = r ^ 2 * entryNormSq M := by
  simp [entryNormSq, Matrix.smul_apply, Complex.normSq_mul]
  ring

def g (delta : ℝ) : ℝ := Real.sqrt (1 / 2 + delta)

def a (delta : ℝ) : ℝ := 1 - 2 * (g delta)^2 - (g delta)^4

def W (delta : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  ((1 - (g delta)^2)^2)⁻¹ • !![ (a delta : ℂ) + 2*I*(g delta)^2,  -(2*(1+I))*(g delta)^3 ;
                                    -(2*(1-I))*(g delta)^3,      (a delta : ℂ) - 2*I*(g delta)^2 ]

theorem g_sq {delta : ℝ} (hd : delta > -1/2) : (g delta)^2 = 1/2 + delta := by
  rw [g, Real.sq_sqrt]
  linarith

theorem one_sub_g_sq {delta : ℝ} (hd : delta > -1/2) :
    1 - (g delta)^2 = 1/2 - delta := by rw [g_sq hd]; ring

theorem denom_ne_zero {delta : ℝ} (hd : delta > -1/2) (hne : delta ≠ 1/2) :
    ((1 - (g delta)^2)^2 : ℝ) ≠ 0 := by
  rw [one_sub_g_sq hd]
  exact pow_ne_zero 2 (sub_ne_zero.mpr (Ne.symm hne))

theorem det_W {delta : ℝ} (hd : delta > -1/2) (hne : delta ≠ 1/2) :
    (W delta).det = 1 := by
  rw [Matrix.det_fin_two]
  simp only [W, Matrix.smul_apply, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Complex.real_smul]
  have hbaseR : 1 - (g delta)^2 ≠ 0 := by
    rw [one_sub_g_sq hd]
    exact sub_ne_zero.mpr (Ne.symm hne)
  have hbase : (1 - (g delta : ℂ)^2) ≠ 0 := by exact_mod_cast hbaseR
  push_cast
  field_simp [hbase]
  rw [a]
  push_cast
  ring_nf
  simp [Complex.I_sq]
  ring

theorem trace_W {delta : ℝ} (hd : delta > -1/2) (hne : delta ≠ 1/2) :
    (W delta).trace = ((2 * (1 - 2 * (1/2 + delta) - (1/2 + delta)^2) /
      (1/2 - delta)^2 : ℝ) : ℂ) := by
  calc
    (W delta).trace = ((2 * a delta / (1 - (g delta)^2)^2 : ℝ) : ℂ) := by
      rw [Matrix.trace_fin_two]
      simp only [W, Matrix.smul_apply, Matrix.of_apply, Matrix.cons_val_zero,
        Matrix.cons_val_one, Complex.real_smul]
      push_cast
      ring
    _ = _ := by
      congr 1
      have hg2 : (g delta)^2 = 1/2 + delta := g_sq hd
      have hg4 : (g delta)^4 = (1/2 + delta)^2 := by
        calc
          (g delta)^4 = ((g delta)^2)^2 := by ring
          _ = _ := by rw [hg2]
      have hdiff : (1/2 - delta : ℝ) ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
      rw [a, hg2, hg4]
      have heq : 1 - (1/2 + delta) = 1/2 - delta := by ring
      rw [heq]
theorem trace_W_zero : (W 0).trace = -2 := by
  rw [trace_W (by norm_num) (by norm_num)]
  norm_num

theorem discriminant {delta : ℝ} (hd : delta > -1/2) (hne : delta ≠ 1/2) :
    (W delta).trace ^ 2 - 4 * (W delta).det =
      ((128 * delta * (1 + 2 * delta)^2 / (1 - 2 * delta)^4 : ℝ) : ℂ) := by
  rw [trace_W hd hne, det_W hd hne]
  have h1R : (1/2 - delta : ℝ) ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  have h2R : (1 - 2 * delta : ℝ) ≠ 0 := by
    intro h
    apply hne
    linarith
  have h1 : (((1/2 - delta : ℝ)) : ℂ) ≠ 0 := by exact_mod_cast h1R
  have h2 : (((1 - 2 * delta : ℝ)) : ℂ) ≠ 0 := by exact_mod_cast h2R
  push_cast at h1 h2
  push_cast
  field_simp [h1, h2]
  ring

theorem g_zero_sq : (g 0)^2 = 1/2 := by
  rw [g_sq (by norm_num)]
  norm_num

theorem g_zero_four : (g 0)^4 = 1/4 := by
  calc
    (g 0)^4 = ((g 0)^2)^2 := by ring
    _ = 1/4 := by rw [g_zero_sq]; norm_num

theorem g_zero_six : (g 0)^6 = 1/8 := by
  calc
    (g 0)^6 = ((g 0)^2)^3 := by ring
    _ = 1/8 := by rw [g_zero_sq]; norm_num

theorem a_zero : a 0 = -1/4 := by
  rw [a, g_zero_sq, g_zero_four]
  norm_num

theorem wall_denominator : (1 - (g 0)^2)^2 = 1/4 := by
  rw [g_zero_sq]
  norm_num

theorem g_zero_sq_complex : (g 0 : ℂ)^2 = 1/2 := by
  rw [← Complex.ofReal_pow, g_zero_sq]
  norm_num

theorem wall_matrix : W 0 + 1 =
    !![4 * I, -8 * (1 + I) * (g 0 : ℂ)^3;
       -8 * (1 - I) * (g 0 : ℂ)^3, -4 * I] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [W, a_zero, g_zero_sq_complex, wall_denominator, Complex.real_smul,
      Matrix.add_apply, Matrix.one_apply] <;> ring

theorem wall_top_left : (W 0 + 1) 0 0 = 4 * I := by
  rw [wall_matrix]
  rfl

theorem wall_nonzero : W 0 + 1 ≠ 0 := by
  intro h
  have h00 := congr_fun (congr_fun h 0) 0
  rw [wall_top_left] at h00
  simp at h00

theorem wall_nilpotent : (W 0 + 1) * (W 0 + 1) = 0 := by
  rw [wall_matrix]
  have hg6 : (g 0 : ℂ)^6 = 1/8 := by
    rw [← Complex.ofReal_pow, g_zero_six]
    norm_num
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
    ring_nf <;> simp [Complex.I_sq, hg6] <;> ring

theorem wall_frobenius : entryNormSq (W 0 + 1) = 64 := by
  rw [wall_matrix]
  simp [entryNormSq, Fin.sum_univ_two, Complex.normSq_apply, ← Complex.ofReal_pow]
  ring_nf
  have hg6 := g_zero_six
  norm_num at hg6 ⊢
  nlinarith

def frobNorm (M : Matrix (Fin 2) (Fin 2) ℂ) : ℝ := Real.sqrt (entryNormSq M)

theorem wall_frobNorm : frobNorm (W 0 + 1) = 8 := by
  rw [frobNorm, wall_frobenius]
  rw [show (64 : ℝ) = 8^2 by norm_num, Real.sqrt_sq (by norm_num)]

theorem continuousAt_entryNormSq_wall :
    ContinuousAt (fun delta => entryNormSq (W delta + 1)) 0 := by
  have hden : (1 - (Real.sqrt (1/2 + 0))^2)^2 ≠ 0 := by
    have hs : (Real.sqrt (1/2 + 0))^2 = 1/2 := by
      rw [add_zero]
      exact Real.sq_sqrt (by norm_num)
    rw [hs]
    norm_num
  unfold entryNormSq W a g
  simp only [Fin.sum_univ_two, Matrix.add_apply, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.one_apply,
    Matrix.smul_apply, Complex.real_smul]
  fun_prop (disch := assumption)

theorem wall_frobenius_tendsto :
    Tendsto (fun delta => Real.sqrt (entryNormSq (W delta + 1)))
      (nhds 0) (nhds 8) := by
  have h := continuousAt_entryNormSq_wall.tendsto.sqrt
  have h8 : Real.sqrt (entryNormSq (W 0 + 1)) = 8 := by exact wall_frobNorm
  simpa only [h8] using h



theorem continuousAt_W_zero : ContinuousAt W 0 := by
  have hden : (1 - (Real.sqrt (1/2 + 0))^2)^2 ≠ 0 := by
    have hs : (Real.sqrt (1/2 + 0))^2 = 1/2 := by
      rw [add_zero]
      exact Real.sq_sqrt (by norm_num)
    rw [hs]
    norm_num
  unfold W a g
  fun_prop (disch := assumption)


theorem wall_entryNormSq_tendsto :
    Tendsto (fun delta => entryNormSq (W delta + 1)) (nhds 0) (nhds 64) := by
  simpa only [wall_frobenius] using continuousAt_entryNormSq_wall.tendsto

/-- The plus spectral projector for a 2 by 2 matrix of determinant one, with
`s > 0` equal to the square root of its discriminant. -/
def spectralProjector (A : Matrix (Fin 2) (Fin 2) ℂ) (s : ℝ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  (s : ℂ)⁻¹ • (A - (((A.trace - (s : ℂ)) / 2) : ℂ) • 1)

/-- The squared Frobenius norm before rescaling by the eigenvalue gap. -/
def spectralCentredNormSq (A : Matrix (Fin 2) (Fin 2) ℂ) (s : ℝ) : ℝ :=
  entryNormSq (A - (((A.trace - (s : ℂ)) / 2) : ℂ) • 1)

theorem entryNormSq_spectralProjector
    (A : Matrix (Fin 2) (Fin 2) ℂ) {D : ℝ} (hD : 0 < D) :
    entryNormSq (spectralProjector A (Real.sqrt D)) =
      spectralCentredNormSq A (Real.sqrt D) / D := by
  have hs : Real.sqrt D ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hD)
  have hs_sq : (Real.sqrt D) ^ 2 = D := Real.sq_sqrt hD.le
  rw [spectralProjector, ← Complex.ofReal_inv, entryNormSq_real_smul]
  rw [inv_pow, hs_sq]
  simp [spectralCentredNormSq, div_eq_mul_inv, mul_comm]

theorem entryNormSq_nonneg (M : Matrix (Fin 2) (Fin 2) ℂ) : 0 ≤ entryNormSq M := by
  unfold entryNormSq
  apply Finset.sum_nonneg
  intro i hi
  apply Finset.sum_nonneg
  intro j hj
  exact Complex.normSq_nonneg _

theorem spectralCentredNormSq_nonneg (A : Matrix (Fin 2) (Fin 2) ℂ) (s : ℝ) :
    0 ≤ spectralCentredNormSq A s := by
  exact entryNormSq_nonneg _

theorem continuous_entryNormSq : Continuous entryNormSq := by
  unfold entryNormSq
  fun_prop

/-- The normalized eigenvalue-gap factor tends to one at the wall. -/
theorem gap_normalized :
    Tendsto
      (fun delta : ℝ =>
        Real.sqrt (128 * delta * (1 + 2 * delta)^2 / (1 - 2 * delta)^4) /
          Real.sqrt (128 * delta))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
  let q : ℝ → ℝ := fun delta => (1 + 2 * delta) / (1 - 2 * delta)^2
  have hq : Tendsto q (nhds 0) (nhds 1) := by
    have hcont : ContinuousAt q 0 := by
      unfold q
      apply ContinuousAt.div
      · fun_prop
      · fun_prop
      · norm_num
    convert hcont.tendsto using 1 <;> norm_num [q]
  have heq :
      (fun delta : ℝ =>
        Real.sqrt (128 * delta * (1 + 2 * delta)^2 / (1 - 2 * delta)^4) /
          Real.sqrt (128 * delta)) =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
        (fun delta => |q delta|) := by
    filter_upwards [self_mem_nhdsWithin] with delta hdelta
    have hd : 0 < delta := hdelta
    have hbase : 0 ≤ 128 * delta := by positivity
    have hsqrt : Real.sqrt (128 * delta) ≠ 0 := by positivity
    have halg :
        128 * delta * (1 + 2 * delta)^2 / (1 - 2 * delta)^4 =
          (128 * delta) * (q delta)^2 := by
      simp only [q, div_eq_mul_inv, mul_pow, ← inv_pow]
      ring
    rw [halg, Real.sqrt_mul hbase, Real.sqrt_sq_eq_abs]
    exact mul_div_cancel_left₀ _ hsqrt
  have hqa : Tendsto (fun delta => |q delta|) (nhds 0) (nhds 1) := by
    convert hq.abs using 1 <;> norm_num
  exact (hqa.mono_left nhdsWithin_le_nhds).congr' heq.symm

/-- Norm form of the centred-projector limit. -/
theorem projector_norm_limit_of_frobenius {N : ℝ → ℝ}
    (hN : Tendsto N (nhds 0) (nhds 64)) :
    Tendsto
      (fun delta => Real.sqrt delta * Real.sqrt
        (N delta / (128 * delta * (1 + 2 * delta)^2 / (1 - 2 * delta)^4)))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (1 / Real.sqrt 2)) := by
  let D : ℝ → ℝ := fun delta =>
    128 * delta * (1 + 2 * delta)^2 / (1 - 2 * delta)^4
  let r : ℝ → ℝ := fun delta => Real.sqrt (D delta) / Real.sqrt (128 * delta)
  have hN' : Tendsto N (nhdsWithin 0 (Set.Ioi 0)) (nhds 64) :=
    hN.mono_left nhdsWithin_le_nhds
  have hNpos : ∀ᶠ delta in nhdsWithin 0 (Set.Ioi 0), 0 < N delta :=
    hN'.eventually (Ioi_mem_nhds (by norm_num : (0 : ℝ) < 64))
  have hsmall : ∀ᶠ (delta : ℝ) in nhdsWithin (0 : ℝ) (Set.Ioi 0), delta < 1 / 2 :=
    nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  have hr : Tendsto r (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
    simpa only [r, D] using gap_normalized
  have hrinv : Tendsto (fun delta => (r delta)⁻¹)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
    simpa using hr.inv₀ one_ne_zero
  have hprod := (hN'.sqrt.mul
    (tendsto_const_nhds : Tendsto (fun _ : ℝ => (1 / Real.sqrt 128 : ℝ)) _ _)).mul hrinv
  have h64 : Real.sqrt (64 : ℝ) = 8 := by
    rw [show (64 : ℝ) = 8^2 by norm_num, Real.sqrt_sq (by norm_num)]
  have h128 : Real.sqrt (128 : ℝ) = 8 * Real.sqrt 2 := by
    rw [show (128 : ℝ) = 64 * 2 by norm_num,
      Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 64), h64]
  have hval :
      (Real.sqrt 64 * (1 / Real.sqrt 128)) * (1 : ℝ) = 1 / Real.sqrt 2 := by
    rw [h64, h128]
    have hs : Real.sqrt 2 ≠ 0 := by positivity
    field_simp
  rw [hval] at hprod
  apply hprod.congr'
  filter_upwards [self_mem_nhdsWithin, hNpos, hsmall] with delta hd hNd hdsmall
  have hd' : 0 < delta := hd
  have hden : 0 < 1 - 2 * delta := by linarith
  have hnum : 0 < 1 + 2 * delta := by linarith
  have hD : 0 < D delta := by
    dsimp [D]
    positivity
  have hB : 0 < 128 * delta := by positivity
  have hsqrtD : Real.sqrt (D delta) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hD)
  have hsqrtB : Real.sqrt (128 * delta) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hB)
  have hsqrtDelta : Real.sqrt delta ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hd')
  have hsqrt128 : Real.sqrt (128 : ℝ) ≠ 0 := by positivity
  dsimp [r]
  rw [Real.sqrt_div hNd.le, Real.sqrt_mul (show (0 : ℝ) ≤ 128 by norm_num)]
  set x := Real.sqrt (N delta)
  set y := Real.sqrt delta
  set z := Real.sqrt (D delta)
  set u := Real.sqrt (128 : ℝ)
  have hy : y ≠ 0 := by simpa only [y] using hsqrtDelta
  have hz : z ≠ 0 := by simpa only [z] using hsqrtD
  have hu : u ≠ 0 := by simpa only [u] using hsqrt128
  change x * (1 / u) * (z / (u * y))⁻¹ = y * (x / z)
  field_simp [hy, hz, hu]
  <;> ring

/-- Correct squared form of the centred-projector limit: the multiplier is
`delta`, not `sqrt delta`. -/
theorem projector_sq_limit_of_frobenius {N : ℝ → ℝ}
    (hN : Tendsto N (nhds 0) (nhds 64)) (hN0 : ∀ delta, 0 ≤ N delta) :
    Tendsto
      (fun delta => delta *
        (N delta / (128 * delta * (1 + 2 * delta)^2 / (1 - 2 * delta)^4)))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (1 / 2)) := by
  have h := (projector_norm_limit_of_frobenius hN).mul
    (projector_norm_limit_of_frobenius hN)
  have hval :
      (1 / Real.sqrt 2 : ℝ) * (1 / Real.sqrt 2) = 1 / 2 := by
    have hs := Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num)
    have hn : Real.sqrt 2 ≠ 0 := by positivity
    field_simp
    nlinarith
  rw [hval] at h
  have hsmall : ∀ᶠ (delta : ℝ) in nhdsWithin (0 : ℝ) (Set.Ioi 0), delta < 1 / 2 :=
    nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin, hsmall] with delta hd hdsmall
  have hdpos : 0 < delta := hd
  have hd' : 0 ≤ delta := hdpos.le
  have hden : 0 < 1 - 2 * delta := by linarith
  have hnum : 0 < 1 + 2 * delta := by linarith
  have hD : 0 < 128 * delta * (1 + 2 * delta)^2 / (1 - 2 * delta)^4 := by
    positivity
  have hNnonneg : 0 ≤ N delta / (128 * delta * (1 + 2 * delta)^2 /
      (1 - 2 * delta)^4) := div_nonneg (hN0 delta) hD.le
  calc
    Real.sqrt delta * Real.sqrt (N delta /
          (128 * delta * (1 + 2 * delta)^2 / (1 - 2 * delta)^4)) *
        (Real.sqrt delta * Real.sqrt (N delta /
          (128 * delta * (1 + 2 * delta)^2 / (1 - 2 * delta)^4))) =
      (Real.sqrt delta * Real.sqrt delta) *
        (Real.sqrt (N delta / (128 * delta * (1 + 2 * delta)^2 /
          (1 - 2 * delta)^4)) * Real.sqrt (N delta /
          (128 * delta * (1 + 2 * delta)^2 / (1 - 2 * delta)^4))) := by ring
    _ = delta * (N delta / (128 * delta * (1 + 2 * delta)^2 /
          (1 - 2 * delta)^4)) := by
      rw [Real.mul_self_sqrt hd', Real.mul_self_sqrt hNnonneg]

/-- Concrete eigenvalue-gap discriminant from the exact wall calculation. -/
def wallDisc (d : ℝ) : ℝ :=
  128 * d * (1 + 2 * d) ^ 2 / (1 - 2 * d) ^ 4

/-- The normalised centred matrix from the prompt. -/
def Phi (d : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  ((Real.sqrt (wallDisc d) : ℂ)⁻¹) • (W d + 1)

theorem entryNormSq_Phi (d : ℝ) (hD : 0 ≤ wallDisc d) :
    entryNormSq (Phi d) = entryNormSq (W d + 1) / wallDisc d := by
  unfold Phi
  rw [← Complex.ofReal_inv, entryNormSq_real_smul, inv_pow, Real.sq_sqrt hD]
  simp [div_eq_mul_inv, mul_comm]

/-- Correct norm form of item 8 for Phi. -/
theorem projector_limit :
    Tendsto (fun d => Real.sqrt d * frobNorm (Phi d))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (1 / Real.sqrt 2)) := by
  have hmain := projector_norm_limit_of_frobenius wall_entryNormSq_tendsto
  apply hmain.congr'
  filter_upwards [self_mem_nhdsWithin] with d hd
  have hdpos : 0 < d := hd
  have hD : 0 ≤ wallDisc d := by
    dsimp [wallDisc]
    positivity
  change Real.sqrt d * Real.sqrt (entryNormSq (W d + 1) / wallDisc d) =
    Real.sqrt d * Real.sqrt (entryNormSq (Phi d))
  rw [entryNormSq_Phi d hD]

/-- Correct squared form: delta multiplies entryNormSq Phi, not sqrt delta. -/
theorem projector_sq_limit :
    Tendsto (fun d => d * entryNormSq (Phi d))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (1 / 2)) := by
  have hmain := projector_sq_limit_of_frobenius wall_entryNormSq_tendsto
    (fun d => entryNormSq_nonneg (W d + 1))
  apply hmain.congr'
  filter_upwards [self_mem_nhdsWithin] with d hd
  have hdpos : 0 < d := hd
  have hD : 0 ≤ wallDisc d := by
    dsimp [wallDisc]
    positivity
  change d * (entryNormSq (W d + 1) / wallDisc d) = d * entryNormSq (Phi d)
  rw [entryNormSq_Phi d hD]

theorem tendsto_wallDisc : Tendsto wallDisc (nhds 0) (nhds 0) := by
  have hc : ContinuousAt wallDisc 0 := by
    unfold wallDisc
    apply ContinuousAt.div
    · fun_prop
    · fun_prop
    · norm_num
  convert hc.tendsto using 1 <;> norm_num [wallDisc]

theorem tendsto_sqrt_wallDisc :
    Tendsto (fun d => Real.sqrt (wallDisc d)) (nhds 0) (nhds 0) := by
  have hc : Tendsto ((fun x : ℝ => Real.sqrt x) ∘ wallDisc) (nhds 0) (nhds 0) := by
    convert (Real.continuous_sqrt.tendsto 0).comp tendsto_wallDisc using 1 <;> simp
  exact hc

theorem spectralCentredNormSq_tendsto_of_wall
    {A : ℝ → Matrix (Fin 2) (Fin 2) ℂ} {A0 : Matrix (Fin 2) (Fin 2) ℂ}
    (hA : Tendsto A (nhds 0) (nhds A0)) (htr : A0.trace = -2)
    (hwall : entryNormSq (A0 + 1) = 64) :
    Tendsto (fun d => spectralCentredNormSq (A d) (Real.sqrt (wallDisc d)))
      (nhds 0) (nhds 64) := by
  have h00 : Tendsto (fun d => A d 0 0) (nhds 0) (nhds (A0 0 0)) :=
    (continuous_apply 0).continuousAt.tendsto.comp
      ((continuous_apply 0).continuousAt.tendsto.comp hA)
  have h11 : Tendsto (fun d => A d 1 1) (nhds 0) (nhds (A0 1 1)) :=
    (continuous_apply 1).continuousAt.tendsto.comp
      ((continuous_apply 1).continuousAt.tendsto.comp hA)
  have htrace : Tendsto (fun d => (A d).trace) (nhds 0) (nhds (A0.trace)) := by
    simpa only [Matrix.trace_fin_two] using h00.add h11
  rw [htr] at htrace
  have hsC : Tendsto (fun d => ((Real.sqrt (wallDisc d) : ℝ) : ℂ))
      (nhds 0) (nhds 0) := by
    exact (Complex.continuous_ofReal.tendsto 0).comp tendsto_sqrt_wallDisc
  have hl := (htrace.sub hsC).div_const (2 : ℂ)
  have hl' : Tendsto (fun d => (((A d).trace - ((Real.sqrt (wallDisc d) : ℝ) : ℂ)) / 2))
      (nhds 0) (nhds (-1)) := by
    convert hl using 1 <;> norm_num
  have hM := hA.sub (hl'.smul (tendsto_const_nhds :
    Tendsto (fun _ : ℝ => (1 : Matrix (Fin 2) (Fin 2) ℂ)) (nhds 0) (nhds 1)))
  have hnorm := continuous_entryNormSq.continuousAt.tendsto.comp hM
  have heval : spectralCentredNormSq A0 0 = 64 := by
    simpa [spectralCentredNormSq, htr] using hwall
  rw [← heval]
  convert hnorm using 1
  · rfl
  · norm_num [spectralCentredNormSq, htr]

/-- The overlap associated with the actual spectral projector of `A d`. -/
def spectralOverlap (A : ℝ → Matrix (Fin 2) (Fin 2) ℂ) (d : ℝ) : ℝ :=
  overlapFromNormSq (entryNormSq (spectralProjector (A d) (Real.sqrt (wallDisc d))))

/-- Conditional on the elementary unnormalised norm continuity, this is the
condition-number limit for the actual spectral projector, not `Phi + I/2`. -/
theorem spectral_kappa_limit_of_centred_norm
    {A : ℝ → Matrix (Fin 2) (Fin 2) ℂ}
    (hN : Tendsto (fun d => spectralCentredNormSq (A d) (Real.sqrt (wallDisc d)))
      (nhds 0) (nhds 64)) :
    Tendsto
      (fun d => Real.sqrt d * ((1 + spectralOverlap A d) *
        Real.sqrt (entryNormSq (spectralProjector (A d) (Real.sqrt (wallDisc d))))))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (Real.sqrt 2)) := by
  let N : ℝ → ℝ := fun d => spectralCentredNormSq (A d) (Real.sqrt (wallDisc d))
  let F : ℝ → ℝ := fun d => N d / wallDisc d
  have hN' : Tendsto N (nhds 0) (nhds 64) := hN
  have hNorm : Tendsto (fun d => Real.sqrt d * Real.sqrt (F d))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (1 / Real.sqrt 2)) := by
    simpa only [F, N, wallDisc] using projector_norm_limit_of_frobenius hN'
  have hF : Tendsto (fun d => d * F d)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (1 / 2)) := by
    simpa only [F, N, wallDisc] using projector_sq_limit_of_frobenius hN'
      (fun d => spectralCentredNormSq_nonneg (A d) (Real.sqrt (wallDisc d)))
  have hsmall : ∀ᶠ (d : ℝ) in nhdsWithin (0 : ℝ) (Set.Ioi 0), d < 1 / 2 :=
    nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  have hPos : ∀ᶠ d in nhdsWithin 0 (Set.Ioi 0), 0 < wallDisc d := by
    filter_upwards [self_mem_nhdsWithin, hsmall] with d hd hdsmall
    have hdpos : 0 < d := hd
    have hden : 0 < 1 - 2 * d := by linarith
    have hnum : 0 < 1 + 2 * d := by linarith
    dsimp [wallDisc]
    positivity
  have hEq : (fun d => entryNormSq (spectralProjector (A d) (Real.sqrt (wallDisc d))))
      =ᶠ[nhdsWithin 0 (Set.Ioi 0)] F := by
    filter_upwards [hPos] with d hd
    exact entryNormSq_spectralProjector (A d) hd
  have hk := kappa_limit_of_projector_norm hF hNorm
  apply hk.congr'
  filter_upwards [hEq] with d hd
  simp only [spectralOverlap, F]
  rw [hd]

/-- Wall-interface form: continuity of the explicit matrix and its two wall
computations give the actual condition-number limit. -/
theorem spectral_kappa_limit_of_wall
    {A : ℝ → Matrix (Fin 2) (Fin 2) ℂ} {A0 : Matrix (Fin 2) (Fin 2) ℂ}
    (hA : Tendsto A (nhds 0) (nhds A0)) (htr : A0.trace = -2)
    (hwall : entryNormSq (A0 + 1) = 64) :
    Tendsto
      (fun d => Real.sqrt d * ((1 + spectralOverlap A d) *
        Real.sqrt (entryNormSq (spectralProjector (A d) (Real.sqrt (wallDisc d))))))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (Real.sqrt 2)) :=
  spectral_kappa_limit_of_centred_norm
    (spectralCentredNormSq_tendsto_of_wall hA htr hwall)

/-- The genuine plus spectral projector, not the prompt's simplified
`Phi + (1/2) • 1` (which omits a trace correction away from the wall). -/
def PplusSpectral (d : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  spectralProjector (W d) (Real.sqrt (wallDisc d))

def wallOverlap (d : ℝ) : ℝ :=
  overlapFromNormSq (entryNormSq (PplusSpectral d))

/-- Item 10 for the actual spectral projector and its exact norm-defined
overlap.  The displayed factor `(1 + wallOverlap d)` is kept separate. -/
theorem kappa_limit :
    Tendsto (fun d => Real.sqrt d * ((1 + wallOverlap d) *
      Real.sqrt (entryNormSq (PplusSpectral d))))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (Real.sqrt 2)) := by
  simpa only [wallOverlap, PplusSpectral, spectralOverlap] using
    (spectral_kappa_limit_of_wall (A := W) (A0 := W 0)
      continuousAt_W_zero.tendsto trace_W_zero wall_frobenius)

end PeelWall

-- Complete axiom audit for every lemma and theorem above.
#print axioms PeelWall.tendsto_inv_normSq
#print axioms PeelWall.overlapFromNormSq_tendsto
#print axioms PeelWall.kappa_limit_of_projector_norm
#print axioms PeelWall.overlap_identity
#print axioms PeelWall.overlapFromNormSq_sq
#print axioms PeelWall.overlapFromNormSq_lt_one
#print axioms PeelWall.overlapFromNormSq_condition_identity
#print axioms PeelWall.entryNormSq_real_smul
#print axioms PeelWall.g_sq
#print axioms PeelWall.one_sub_g_sq
#print axioms PeelWall.denom_ne_zero
#print axioms PeelWall.det_W
#print axioms PeelWall.trace_W
#print axioms PeelWall.trace_W_zero
#print axioms PeelWall.discriminant
#print axioms PeelWall.g_zero_sq
#print axioms PeelWall.g_zero_four
#print axioms PeelWall.g_zero_six
#print axioms PeelWall.a_zero
#print axioms PeelWall.wall_denominator
#print axioms PeelWall.g_zero_sq_complex
#print axioms PeelWall.wall_matrix
#print axioms PeelWall.wall_top_left
#print axioms PeelWall.wall_nonzero
#print axioms PeelWall.wall_nilpotent
#print axioms PeelWall.wall_frobenius
#print axioms PeelWall.wall_frobNorm
#print axioms PeelWall.continuousAt_entryNormSq_wall
#print axioms PeelWall.wall_frobenius_tendsto
#print axioms PeelWall.continuousAt_W_zero
#print axioms PeelWall.wall_entryNormSq_tendsto
#print axioms PeelWall.entryNormSq_spectralProjector
#print axioms PeelWall.entryNormSq_nonneg
#print axioms PeelWall.spectralCentredNormSq_nonneg
#print axioms PeelWall.continuous_entryNormSq
#print axioms PeelWall.gap_normalized
#print axioms PeelWall.projector_norm_limit_of_frobenius
#print axioms PeelWall.projector_sq_limit_of_frobenius
#print axioms PeelWall.entryNormSq_Phi
#print axioms PeelWall.projector_limit
#print axioms PeelWall.projector_sq_limit
#print axioms PeelWall.tendsto_wallDisc
#print axioms PeelWall.tendsto_sqrt_wallDisc
#print axioms PeelWall.spectralCentredNormSq_tendsto_of_wall
#print axioms PeelWall.spectral_kappa_limit_of_centred_norm
#print axioms PeelWall.spectral_kappa_limit_of_wall
#print axioms PeelWall.kappa_limit
