import Mathlib.Analysis.Sobolev.SobolevEmbeddings
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Calculus.Deriv

open Real MeasureTheory Set

variable (ℓ σ : ℝ) (hℓ : 0 < ℓ) (hσ : 0 < σ)

def gaussian_weight (x : ℝ) : ℝ := exp (- x^2 / σ^2)

def stepanov_norm (u : ℝ → ℝ) (x₀ : ℝ) : ℝ :=
  ∫ (y : ℝ) in x₀ .. (x₀ + ℓ), gaussian_weight (y - x₀) * (u y)^2 ∂ volume

def sobolev_stepanov_norm (u : ℝ → ℝ) (x₀ : ℝ) : ℝ :=
  sqrt (stepanov_norm ℓ σ u x₀ ^ 2 + stepanov_norm ℓ σ (deriv u) x₀ ^ 2)

lemma gaussian_weight_min_on_interval (x₀ : ℝ) (y : ℝ) (hy : y ∈ Icc (x₀ - ℓ/2) (x₀ + ℓ/2)) :
    gaussian_weight (y - x₀) ≥ exp (- (ℓ/2)^2 / σ^2) :=
by
  rw [gaussian_weight, exp_le_exp]
  have : |y - x₀| ≤ ℓ/2 := by
    rw [mem_Icc] at hy
    rw [abs_le, neg_le, le_neg]
    constructor <;> linarith
  rw [le_div_iff (sq_pos_of_pos hσ), neg_le_neg_iff, sq_le_sq]
  exact this

theorem sobolev_stepanov_inequality (u : ℝ → ℝ) (hu : ContDiff ℝ 2 u) (x₀ : ℝ) :
    |u x₀| ≤ (2 / sqrt ℓ) * sqrt (exp (ℓ^2 / (4 * σ^2))) * sobolev_stepanov_norm ℓ σ u x₀ :=
by
  let I := Icc (x₀ - ℓ/2) (x₀ + ℓ/2)
  have I_len : volume I = ℓ := by simp [I]

  -- Classical 1D Sobolev inequality
  have hu1 : ContDiffOn ℝ 1 u I := hu.contDiffOn (le_refl 1) I
  have sobolev_1d : ‖u.restrict I‖_L∞ ≤ (2 / sqrt ℓ) * ‖u.restrict I‖_L² + (sqrt ℓ / 2) * ‖(deriv u).restrict I‖_L² :=
    by
    apply SobolevEmbeddings.one_dimensional_inequality (hu1.differentiableOn) I_len
    exact (Icc_compact _ _).isCompact.isMeasurable

  -- Lower bound of Gaussian weight
  let C0 := exp (- (ℓ/2)^2 / σ^2)
  have C0_pos : 0 < C0 := exp_pos _

  have L2_le_step : ‖u.restrict I‖_L² ≤ sqrt (exp (ℓ^2 / (4 * σ^2))) * stepanov_norm ℓ σ u x₀ :=
  by
    rw [sqrt_exp (ℓ^2 / (4 * σ^2)), ← exp_half (ℓ^2 / (4 * σ^2))]
    have : ∫ y in I, (u y)^2 ∂ volume ≤ (exp (ℓ^2 / (4 * σ^2))) * ∫ y in I, gaussian_weight (y - x₀) * (u y)^2 ∂ volume :=
      by
      apply integral_le_integral_of_le (by measurability) (by measurability) _ _
      · intro y hy
        rw [mul_comm, ← le_div_iff' (exp_pos _)]
        refine le_trans ?_ (one_le_exp_iff.mpr (by positivity))
        exact gaussian_weight_min_on_interval ℓ σ hσ x₀ y hy
      · exact measurableSet_Icc
    have step_estimate : ∫ y in I, gaussian_weight (y - x₀) * (u y)^2 ∂ volume ≤ stepanov_norm ℓ σ u x₀ ^ 2 :=
      by
      rw [stepanov_norm, ← integral_Icc_eq_integral_Ioc]
      apply le_of_eq (by simp)
    rw [pow_two] at step_estimate
    linarith

  have L2_le_step_deriv : ‖(deriv u).restrict I‖_L² ≤ sqrt (exp (ℓ^2 / (4 * σ^2))) * stepanov_norm ℓ σ (deriv u) x₀ :=
  by
    -- same proof as above for derivative
    rw [sqrt_exp (ℓ^2 / (4 * σ^2)), ← exp_half (ℓ^2 / (4 * σ^2))]
    have : ∫ y in I, (deriv u y)^2 ∂ volume ≤ (exp (ℓ^2 / (4 * σ^2))) * ∫ y in I, gaussian_weight (y - x₀) * (deriv u y)^2 ∂ volume :=
      by
      apply integral_le_integral_of_le (by measurability) (by measurability) _ _
      · intro y hy
        rw [mul_comm, ← le_div_iff' (exp_pos _)]
        refine le_trans ?_ (one_le_exp_iff.mpr (by positivity))
        exact gaussian_weight_min_on_interval ℓ σ hσ x₀ y hy
      · exact measurableSet_Icc
    have step_estimate : ∫ y in I, gaussian_weight (y - x₀) * (deriv u y)^2 ∂ volume ≤ stepanov_norm ℓ σ (deriv u) x₀ ^ 2 :=
      by
      rw [stepanov_norm, ← integral_Icc_eq_integral_Ioc]
      apply le_of_eq (by simp)
    rw [pow_two] at step_estimate
    linarith

  -- Combine
  let A := (2 / sqrt ℓ) * sqrt (exp (ℓ^2 / (4 * σ^2)))
  let B := (sqrt ℓ / 2) * sqrt (exp (ℓ^2 / (4 * σ^2)))
  have bound : |u x₀| ≤ A * stepanov_norm ℓ σ u x₀ + B * stepanov_norm ℓ σ (deriv u) x₀ :=
    by
    refine (sobolev_1d.trans (add_le_add (mul_le_mul_of_nonneg_left (L2_le_step) (by positivity))
                                         (mul_le_mul_of_nonneg_left (L2_le_step_deriv) (by positivity))))
    all_goals positivity

  have cauchy : A * stepanov_norm ℓ σ u x₀ + B * stepanov_norm ℓ σ (deriv u) x₀ ≤
                sqrt (A^2 + B^2) * sqrt (stepanov_norm ℓ σ u x₀ ^ 2 + stepanov_norm ℓ σ (deriv u) x₀ ^ 2) :=
    by
    apply Real.sqrt_mul_self_add_mul_self_le

  have final_constant : sqrt (A^2 + B^2) = (2 / sqrt ℓ) * sqrt (exp (ℓ^2 / (4 * σ^2))) :=
    by
    have A2 : A^2 = (4 / ℓ) * exp (ℓ^2 / (4 * σ^2)) := by field_simp [A]; ring
    have B2 : B^2 = (ℓ / 4) * exp (ℓ^2 / (4 * σ^2)) := by field_simp [B]; ring
    rw [A2, B2, ← add_mul, sqrt_mul (add_nonneg (by positivity) (by positivity)) (exp_pos _).le]
    have h : sqrt (4/ℓ + ℓ/4) = (2 / sqrt ℓ) * sqrt (1 + ℓ^2/16) := by
      rw [sqrt_div, sqrt_mul, sqrt_eq_abs] <;> positivity
      simp [sqrt (4/ℓ + ℓ/4)]
    rw [h]
    ring_nf
    rw [← mul_assoc, mul_comm _ (sqrt (exp (ℓ^2 / (4 * σ^2)))), mul_assoc]
    exact le_of_eq rfl

  rw [final_constant] at cauchy
  exact bound.trans (cauchy.trans (by rw [sobolev_stepanov_norm]))
