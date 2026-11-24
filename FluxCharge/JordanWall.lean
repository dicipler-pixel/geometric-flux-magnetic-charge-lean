import Mathlib

/-!
# `FluxCharge.JordanWall` — what an exceptional point does to a two-level operator

Three statements the black-hole manuscript uses in words, proved here in the smallest setting where
they are exact. Imports Mathlib only; nothing depends on the monopole chain.

* **The Jordan propagator carries a term linear in time.** For the nilpotent `N = !![0,1;0,0]`
  (`N * N = 0`, `N ≠ 0`) and `Phi lam t = exp (lam * t) • (1 + t • N)`, the entrywise derivative is
  `((lam • 1 + N) * Phi lam t)`, the diagonal entries are `exp (lam * t)`, the upper-right entry is
  `t * exp (lam * t)`, the lower-left entry is `0`, and for `t ≠ 0` the propagator is not a scalar
  multiple of the identity.

* **The single projector diverges, the pair does not.** For `A = !![lam + g, b; 0, lam]` with
  `g ≠ 0`, the spectral projectors `P±` are explicit; `entryNormSq P+ = 1 + ‖b‖^2/‖g‖^2`, so
  `‖P+‖ * gap → ‖b‖` (the manuscript's "the divergence constant of a single projector is the Jordan
  coupling"), while `P+ + P- = 1` has determinant `1` and squared entry norm `2`: the pair stays
  finite at the wall.

* **A two-by-two wall is a normal form.** Over any nontrivial commutative ring, `trace W = 2 * lam`
  and `det W = lam^2` force `charpoly W = (X - lam)^2` and hence `(W - lam • 1)^2 = 0`, with
  `W - lam • 1` either zero or a nonzero nilpotent. The model `Wm d = !![ -1, 1; d, -1]` has
  discriminant `4 d`, eigenvector criterion `(mu + 1)^2 = d`, and gap `2 sqrt |d|`. The wall at
  `d = 0` is the *centred* matrix `Wm 0 - (-1) • 1`, which is nonzero with square zero — `Wm 0`
  itself is not nilpotent, and the file says so rather than asserting the false version.

The peel wall's instance (`trace (W+1) = 0`, `(W+1)^2 = 0`, `W+1 ≠ 0`) is the third part at
`lam = -1`; instantiating a specific matrix `W(delta)` is a matter of supplying its trace and
determinant.
-/

open scoped Matrix BigOperators
open Filter

set_option maxHeartbeats 800000

noncomputable section

namespace JordanWall

/-- The nonzero nilpotent in the elementary complex Jordan block. -/
def N : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 0, 0]

/-- The Jordan-block propagator, including its term linear in time. -/
def Phi (lam : ℂ) (t : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  Complex.exp (lam * (t : ℂ)) • (1 + (t : ℂ) • N)

theorem N_sq : N * N = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [N, Matrix.mul_apply, Fin.sum_univ_two]

theorem N_ne_zero : N ≠ 0 := by
  intro h
  have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 1) h
  norm_num [N] at h01

theorem Phi_deriv (lam : ℂ) (t : ℝ) (i j : Fin 2) :
    HasDerivAt (fun s => Phi lam s i j)
      (((lam • (1 : Matrix (Fin 2) (Fin 2) ℂ) + N) * Phi lam t) i j) t := by
  have hlin : HasDerivAt (fun z : ℂ => lam * z) lam (t : ℂ) := by
    simpa using (hasDerivAt_id (t : ℂ)).const_mul lam
  have hexpC : HasDerivAt (fun z : ℂ => Complex.exp (lam * z))
      (Complex.exp (lam * (t : ℂ)) * lam) (t : ℂ) :=
    (Complex.hasDerivAt_exp (lam * (t : ℂ))).comp (t : ℂ) hlin
  have hexp : HasDerivAt (fun s : ℝ => Complex.exp (lam * (s : ℂ)))
      (Complex.exp (lam * (t : ℂ)) * lam) t := hexpC.comp_ofReal
  have hoffC : HasDerivAt (fun z : ℂ => z * Complex.exp (lam * z))
      (1 * Complex.exp (lam * (t : ℂ)) +
        (t : ℂ) * (Complex.exp (lam * (t : ℂ)) * lam)) (t : ℂ) :=
    (hasDerivAt_id (t : ℂ)).mul hexpC
  have hoff : HasDerivAt (fun s : ℝ => (s : ℂ) * Complex.exp (lam * (s : ℂ)))
      (1 * Complex.exp (lam * (t : ℂ)) +
        (t : ℂ) * (Complex.exp (lam * (t : ℂ)) * lam)) t := hoffC.comp_ofReal
  fin_cases i <;> fin_cases j
  · convert hexp using 1 <;>
      simp [Phi, N, Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  · convert hoff using 1 <;>
      simp [Phi, N, Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  · convert (hasDerivAt_const t (0 : ℂ)) using 1 <;>
      simp [Phi, N, Matrix.mul_apply, Fin.sum_univ_two]
  · convert hexp using 1 <;>
      simp [Phi, N, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- The off-diagonal entry is the promised term linear in time. -/
theorem Phi_linear_term (lam : ℂ) (t : ℝ) :
    Phi lam t 0 1 = (t : ℂ) * Complex.exp (lam * (t : ℂ)) ∧
    Phi lam t 0 0 = Complex.exp (lam * (t : ℂ)) ∧
    Phi lam t 1 1 = Complex.exp (lam * (t : ℂ)) ∧
    Phi lam t 1 0 = 0 := by
  simp [Phi, N]
  ring

theorem Phi_not_exponential_only (lam : ℂ) {t : ℝ} (ht : t ≠ 0) :
    Phi lam t ≠ Complex.exp (lam * (t : ℂ)) •
      (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  intro h
  have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 1) h
  simp [Phi, N] at h01
  exact ht h01

/-- The triangular family with eigenvalue gap `g` and coupling `b`. -/
def A (g b lam : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := !![lam + g, b; 0, lam]

def Pplus (g b lam : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (1 / g) • (A g b lam - lam • 1)

def Pminus (g b lam : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  1 - (1 / g) • (A g b lam - lam • 1)

theorem eigenvalues (g b lam : ℂ) :
    (A g b lam).charpoly = (Polynomial.X - Polynomial.C (lam + g)) *
      (Polynomial.X - Polynomial.C lam) := by
  rw [Matrix.charpoly_fin_two]
  simp [A, Matrix.trace_fin_two_of, Matrix.det_fin_two_of]
  ring

theorem Pplus_eq {g : ℂ} (hg : g ≠ 0) (b lam : ℂ) :
    Pplus g b lam = !![1, b / g; 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Pplus, A, div_eq_mul_inv, hg] <;> ring

theorem Pminus_eq {g : ℂ} (hg : g ≠ 0) (b lam : ℂ) :
    Pminus g b lam = !![0, -(b / g); 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Pminus, A, div_eq_mul_inv, hg] <;> ring

theorem Pplus_idem {g : ℂ} (hg : g ≠ 0) (b lam : ℂ) :
    Pplus g b lam * Pplus g b lam = Pplus g b lam := by
  rw [Pplus_eq hg]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem Pminus_idem {g : ℂ} (hg : g ≠ 0) (b lam : ℂ) :
    Pminus g b lam * Pminus g b lam = Pminus g b lam := by
  rw [Pminus_eq hg]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem Pplus_add_Pminus (g b lam : ℂ) :
    Pplus g b lam + Pminus g b lam = 1 := by
  simp [Pplus, Pminus]

theorem Pplus_mul_Pminus {g : ℂ} (hg : g ≠ 0) (b lam : ℂ) :
    Pplus g b lam * Pminus g b lam = 0 := by
  rw [Pplus_eq hg, Pminus_eq hg]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem A_mul_Pplus {g : ℂ} (hg : g ≠ 0) (b lam : ℂ) :
    A g b lam * Pplus g b lam = (lam + g) • Pplus g b lam := by
  rw [Pplus_eq hg]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [A, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem A_mul_Pminus {g : ℂ} (hg : g ≠ 0) (b lam : ℂ) :
    A g b lam * Pminus g b lam = lam • Pminus g b lam := by
  rw [Pminus_eq hg]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [A, Matrix.mul_apply, Fin.sum_univ_two, div_eq_mul_inv, hg] <;>
    field_simp [hg] <;> ring

/-- Squared Frobenius norm, written directly as the sum over entries. -/
def entryNormSq (M : Matrix (Fin 2) (Fin 2) ℂ) : ℝ :=
  ∑ i, ∑ j, ‖M i j‖ ^ 2

/-- Frobenius norm associated with `entryNormSq`. -/
def frobeniusNorm (M : Matrix (Fin 2) (Fin 2) ℂ) : ℝ :=
  Real.sqrt (entryNormSq M)

theorem projector_norm {g : ℂ} (hg : g ≠ 0) (b lam : ℂ) :
    entryNormSq (Pplus g b lam) = 1 + ‖b‖ ^ 2 / ‖g‖ ^ 2 := by
  rw [Pplus_eq hg]
  simp [entryNormSq, Fin.sum_univ_two, norm_div, div_pow]

theorem projector_frobeniusNorm {g : ℂ} (hg : g ≠ 0) (b lam : ℂ) :
    frobeniusNorm (Pplus g b lam) = Real.sqrt (1 + ‖b‖ ^ 2 / ‖g‖ ^ 2) := by
  rw [frobeniusNorm, projector_norm hg]

/-- Multiplying the diverging projector norm by the gap recovers `|b|`. -/
theorem divergence_constant (b : ℝ) :
    Tendsto (fun g : ℝ => Real.sqrt (1 + ‖b‖ ^ 2 / ‖g‖ ^ 2) * ‖g‖)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds ‖b‖) := by
  have hid : (fun g : ℝ => Real.sqrt (1 + ‖b‖ ^ 2 / ‖g‖ ^ 2) * ‖g‖)
      =ᶠ[nhdsWithin 0 (Set.Ioi 0)] (fun g => Real.sqrt (g ^ 2 + ‖b‖ ^ 2)) := by
    filter_upwards [self_mem_nhdsWithin] with g hg
    have hgpos : 0 < g := hg
    have hg0 : 0 ≤ g := hgpos.le
    have hgne : g ≠ 0 := ne_of_gt hgpos
    simp only [Real.norm_eq_abs, abs_of_pos hgpos]
    calc
      Real.sqrt (1 + ‖b‖ ^ 2 / g ^ 2) * g =
          Real.sqrt ((1 + ‖b‖ ^ 2 / g ^ 2) * g ^ 2) := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hg0]
      _ = Real.sqrt (g ^ 2 + ‖b‖ ^ 2) := by
        congr 1
        field_simp
        <;> ring
  have hlim : Tendsto (fun g : ℝ => Real.sqrt (g ^ 2 + ‖b‖ ^ 2))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds ‖b‖) := by
    have h : Tendsto (fun g : ℝ => g ^ 2 + ‖b‖ ^ 2)
        (nhds 0) (nhds (0 ^ 2 + ‖b‖ ^ 2)) :=
      (tendsto_id.pow 2).add_const (‖b‖ ^ 2)
    have hs := h.sqrt
    have hs' := hs.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
    simpa [Real.norm_eq_abs, Real.sqrt_sq_eq_abs] using hs'
  exact hlim.congr' hid.symm

theorem pair_finite {g : ℂ} (hg : g ≠ 0) (b lam : ℂ) :
    entryNormSq (Pplus g b lam + Pminus g b lam) = 2 ∧
    Matrix.trace (Pplus g b lam + Pminus g b lam) = 2 := by
  rw [Pplus_add_Pminus]
  constructor
  · norm_num [entryNormSq, Fin.sum_univ_two, Matrix.one_apply]
  · simp [Matrix.trace_fin_two, Matrix.one_apply]

theorem pair_frobeniusNorm (g b lam : ℂ) :
    frobeniusNorm (Pplus g b lam + Pminus g b lam) = Real.sqrt 2 := by
  rw [Pplus_add_Pminus]
  norm_num [frobeniusNorm, entryNormSq, Fin.sum_univ_two, Matrix.one_apply]

/-- The full pair is the identity, so its determinant remains `1` at the wall. -/
theorem pair_det (g b lam : ℂ) :
    Matrix.det (Pplus g b lam + Pminus g b lam) = 1 := by
  rw [Pplus_add_Pminus]
  exact Matrix.det_one

/-- Cayley--Hamilton at a repeated-eigenvalue wall, directly from trace and determinant. -/
theorem wall_nilpotent (W : Matrix (Fin 2) (Fin 2) ℂ) (lam : ℂ)
    (htr : Matrix.trace W = 2 * lam) (hdet : Matrix.det W = lam ^ 2) :
    (W - lam • 1) * (W - lam • 1) = 0 := by
  simp only [Matrix.trace_fin_two] at htr
  simp only [Matrix.det_fin_two] at hdet
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.sub_apply,
      Matrix.smul_apply, Matrix.one_apply]
  · linear_combination W 0 0 * htr - hdet
  · linear_combination W 0 1 * htr
  · linear_combination W 1 0 * htr
  · linear_combination W 1 1 * htr - hdet

theorem wall_dichotomy (W : Matrix (Fin 2) (Fin 2) ℂ) (lam : ℂ)
    (htr : Matrix.trace W = 2 * lam) (hdet : Matrix.det W = lam ^ 2) :
    W = lam • 1 ∨
      (W - lam • 1 ≠ 0 ∧ (W - lam • 1) * (W - lam • 1) = 0) := by
  by_cases h : W = lam • 1
  · exact Or.inl h
  · refine Or.inr ⟨?_, wall_nilpotent W lam htr hdet⟩
    intro hzero
    apply h
    exact sub_eq_zero.mp hzero

/-- The real-parameter wall model, embedded in complex two-by-two matrices. -/
def Wm (d : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := !![-1, 1; d, -1]

def modelEigenvector (mu : ℂ) : Fin 2 → ℂ := ![1, mu + 1]

theorem model_wall_basic (d : ℂ) :
    Matrix.trace (Wm d) = -2 ∧ Matrix.det (Wm d) = 1 - d ∧
    (Matrix.trace (Wm d)) ^ 2 - 4 * Matrix.det (Wm d) = 4 * d := by
  simp only [Wm, Matrix.trace_fin_two_of, Matrix.det_fin_two_of]
  constructor
  · ring
  · constructor <;> ring

theorem model_eigenvector_ne_zero (mu : ℂ) : modelEigenvector mu ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  norm_num [modelEigenvector] at h0

/-- The eigenvector equation unfolds exactly as `(mu + 1)^2 = d`. -/
theorem model_eigenvector_iff (d mu : ℂ) :
    (Wm d).mulVec (modelEigenvector mu) = mu • modelEigenvector mu ↔
      (mu + 1) ^ 2 = d := by
  constructor
  · intro h
    have h1 := congrFun h 1
    simp [Wm, modelEigenvector, Matrix.mulVec, Fin.sum_univ_two] at h1
    linear_combination -h1
  · intro h
    funext i
    fin_cases i
    · simp [Wm, modelEigenvector, Matrix.mulVec, Fin.sum_univ_two]
    · simp [Wm, modelEigenvector, Matrix.mulVec, Fin.sum_univ_two]
      linear_combination -h

/-- At `d = 0`, the shifted model is a nonzero square-zero matrix. -/
theorem model_wall :
    Wm 0 - (-1 : ℂ) • 1 ≠ 0 ∧
    (Wm 0 - (-1 : ℂ) • 1) * (Wm 0 - (-1 : ℂ) • 1) = 0 := by
  constructor
  · intro h
    have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 1) h
    norm_num [Wm] at h01
  · apply wall_nilpotent (Wm 0) (-1)
    · norm_num [Wm, Matrix.trace_fin_two_of]
    · norm_num [Wm, Matrix.det_fin_two_of]

private theorem quadratic_roots (z mu : ℂ) :
    (mu + 1) ^ 2 = z ^ 2 ↔ mu = -1 + z ∨ mu = -1 - z := by
  rw [sq_eq_sq_iff_eq_or_eq_neg]
  constructor
  · rintro (h | h)
    · left
      linear_combination h
    · right
      linear_combination h
  · rintro (h | h)
    · left
      linear_combination h
    · right
      linear_combination h

/-- For positive real `d`, the two roots are real and are `-1 ± sqrt d`. -/
theorem model_roots_pos {d : ℝ} (hd : 0 < d) (mu : ℂ) :
    (mu + 1) ^ 2 = (d : ℂ) ↔
      mu = -1 + (Real.sqrt d : ℂ) ∨ mu = -1 - (Real.sqrt d : ℂ) := by
  have hs : ((Real.sqrt d : ℂ)) ^ 2 = (d : ℂ) := by
    norm_cast
    exact Real.sq_sqrt hd.le
  rw [← hs]
  exact quadratic_roots _ _

theorem model_roots_pos_distinct {d : ℝ} (hd : 0 < d) :
    (-1 + (Real.sqrt d : ℂ)) ≠ -1 - (Real.sqrt d : ℂ) := by
  have hs : (Real.sqrt d : ℂ) ≠ 0 := by
    norm_cast
    exact ne_of_gt (Real.sqrt_pos.2 hd)
  intro h
  apply hs
  linear_combination h / 2

/-- For negative real `d`, the roots are `-1 ± I * sqrt (-d)`. -/
theorem model_roots_neg {d : ℝ} (hd : d < 0) (mu : ℂ) :
    (mu + 1) ^ 2 = (d : ℂ) ↔
      mu = -1 + Complex.I * (Real.sqrt (-d) : ℂ) ∨
      mu = -1 - Complex.I * (Real.sqrt (-d) : ℂ) := by
  have hs : (Complex.I * (Real.sqrt (-d) : ℂ)) ^ 2 = (d : ℂ) := by
    rw [mul_pow, Complex.I_sq]
    have hr : ((Real.sqrt (-d) : ℂ)) ^ 2 = ((-d : ℝ) : ℂ) := by
      norm_cast
      exact Real.sq_sqrt (neg_nonneg.mpr hd.le)
    rw [hr]
    push_cast
    ring
  rw [← hs]
  exact quadratic_roots _ _

/-- The nonnegative gap associated with either sign branch of the model. -/
def modelGap (d : ℝ) : ℝ := 2 * Real.sqrt |d|

theorem model_gap_pos {d : ℝ} (hd : 0 < d) :
    ‖(-1 + (Real.sqrt d : ℂ)) - (-1 - (Real.sqrt d : ℂ))‖ = modelGap d := by
  have h : (-1 + (Real.sqrt d : ℂ)) - (-1 - (Real.sqrt d : ℂ)) =
      ((2 * Real.sqrt d : ℝ) : ℂ) := by
    push_cast
    ring
  rw [h, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : 0 ≤ 2 * Real.sqrt d)]
  simp [modelGap, abs_of_pos hd]

theorem model_gap_neg {d : ℝ} (hd : d < 0) :
    ‖(-1 + Complex.I * (Real.sqrt (-d) : ℂ)) -
      (-1 - Complex.I * (Real.sqrt (-d) : ℂ))‖ = modelGap d := by
  have h : (-1 + Complex.I * (Real.sqrt (-d) : ℂ)) -
      (-1 - Complex.I * (Real.sqrt (-d) : ℂ)) =
      Complex.I * ((2 * Real.sqrt (-d) : ℝ) : ℂ) := by
    push_cast
    ring
  rw [h, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ 2 * Real.sqrt (-d))]
  simp [modelGap, abs_of_neg hd]

/-- The square-root gap law, including its normalized finite slope `2`. -/
theorem gap_sqrt_law {d : ℝ} (hd : d ≠ 0) :
    (modelGap d) ^ 2 = 4 * |d| ∧ modelGap d / Real.sqrt |d| = 2 := by
  have hs : Real.sqrt |d| ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (abs_pos.2 hd))
  constructor
  · simp only [modelGap, mul_pow, Real.sq_sqrt (abs_nonneg d)]
    ring
  · simp only [modelGap]
    field_simp

end JordanWall
