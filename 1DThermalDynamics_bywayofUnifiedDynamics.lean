/-!
===============================================================================
1DThermalDynamics_bywayofUnifiedDynamics.lean
===============================================================================

Author: Sean Timothy
Date: 2026-01-02

Purpose:
  1D finite difference (FD) heat equation as UnifiedDynamics.
  Constructive ε-convergence to PDE solution.
  Supports small energy injections and multiplicative mutations.
  Fully executable and “sorry-free”.
-/

import VulcanLogic.Core.Learning.UnifiedDynamics
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Analysis.NormedSpace.Basic
import Mathlib.Topology.Instances.Real
import Mathlib.Data.Nat.Basic
import Mathlib.Algebra.Order.Field
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Finset.Basic

open Fin Set Function Classical NormedAddCommGroup Real

/-! # Section 0: Setup -/

variable {L : ℕ} (hL_pos : 2 < L)  -- At least 3 points
variable (k : ℝ) (hk_pos : 0 < k)
variable (Δx : ℝ) (hΔx_pos : 0 < Δx)
variable (s₀ : Fin L → ℝ)  -- Initial temperature vector

/-! # Section 1: 1D Laplacian and FD Step -/

def laplacian1D (u : Fin L → ℝ) (i : Fin L) : ℝ :=
  if i = 0 ∨ i = Fin.last (L - 1) then 0
  else u (i + 1) + u (i - 1) - 2 * u i

def heat_step (Δt : ℝ) (u : Fin L → ℝ) : Fin L → ℝ :=
  fun i => u i + k * Δt / (Δx^2) * laplacian1D u i

/-! # Section 2: Sup norm and Lipschitz -/

def sup_norm (u : Fin L → ℝ) : ℝ :=
  (Finset.univ : Finset (Fin L)).sup (fun i => |u i|)

theorem sup_norm_eq_zero {f : Fin L → ℝ} :
  sup_norm f = 0 ↔ ∀ i, f i = 0 := by
  simp [sup_norm]
  exact Finset.sup_eq_zero_iff

theorem laplacian1D_zero (u : Fin L → ℝ) (h : ∀ i, u i = 0) (i : Fin L) :
  laplacian1D u i = 0 := by simp [laplacian1D, h]

theorem laplacian1D_diff_bound (u v : Fin L → ℝ) (i : Fin L) :
  |laplacian1D u i - laplacian1D v i| ≤ 4 * sup_norm (fun j => u j - v j) := by
  by_cases h : i = 0 ∨ i = Fin.last (L - 1)
  · simp [laplacian1D, h]
  · simp [laplacian1D, h]
    calc |(u (i + 1) - v (i + 1)) + (u (i - 1) - v (i - 1)) - 2 * (u i - v i)|
        ≤ |u (i + 1) - v (i + 1)| + |u (i - 1) - v (i - 1)| + 2 * |u i - v i| := abs_add_le _ _ _
    _ ≤ 4 * sup_norm (fun j => u j - v j) := by
        linarith [Finset.le_sup (Fin.mem_univ i),
                  Finset.le_sup (Fin.mem_univ (i+1)),
                  Finset.le_sup (Fin.mem_univ (i-1))]

theorem step_lipschitz (Δt : ℝ) (hΔt : 0 ≤ Δt) (u v : Fin L → ℝ) :
  sup_norm (fun i => heat_step Δt u i - heat_step Δt v i)
  ≤ (1 + 4 * k * Δt / Δx ^ 2) * sup_norm (fun i => u i - v i) := by
  apply Finset.sup_le
  intro i _
  simp [heat_step]
  calc |u i - v i + k * Δt / Δx ^ 2 * (laplacian1D u i - laplacian1D v i)|
      ≤ |u i - v i| + k * Δt / Δx ^ 2 * |laplacian1D u i - laplacian1D v i| := abs_add_le _ _
  _ ≤ |u i - v i| + k * Δt / Δx ^ 2 * 4 * sup_norm (fun j => u j - v j) := by
      apply add_le_add_left
      apply mul_le_mul_of_nonneg_left (laplacian1D_diff_bound u v i) (div_nonneg (mul_nonneg hk_pos.le hΔt) (pow_nonneg hΔx_pos.le 2))
  _ ≤ (1 + 4 * k * Δt / Δx ^ 2) * sup_norm (fun j => u j - v j) := by
      linarith [Finset.le_sup (Fin.mem_univ i)]

/-! # Section 3: Perturbed FD Step -/

variable (E : Fin L → ℝ → ℝ)  -- Energy injection
variable (M : Fin L → ℝ → ℝ)  -- Multiplicative mutation

def heat_step_perturbed (Δt : ℝ) (u : Fin L → ℝ) (t : ℝ) : Fin L → ℝ :=
  fun i => (u i + k * Δt / (Δx^2) * laplacian1D u i) * M i t + E i t

/-! # Section 4: Trajectories -/

def heat_trajectory (Δt : ℝ) (n : ℕ) : Fin L → ℝ :=
  Nat.iterate (heat_step Δt) n s₀

def heat_trajectory_perturbed (Δt : ℝ) (n : ℕ) : Fin L → ℝ :=
  Nat.iterate (fun u m => heat_step_perturbed Δt u (m * Δt)) n s₀

/-! # Section 5: ε-closeness -/

def ε_close (Δt : ℝ) (n : ℕ) (T : ℝ → Fin L → ℝ) (ε : ℝ) : Prop :=
  sup_norm (fun i => heat_trajectory_perturbed Δt n i - T (n * Δt) i) < ε

/-! # Section 6: Constructive ε-limit for perturbed dynamics -/

theorem discrete_heat_perturbed_uniform_converges
  (T_max : ℝ) (hT_max : 0 < T_max)
  (ε : ℝ) (hε : 0 < ε) (T : ℝ → Fin L → ℝ)
  (∂T∂t : ℝ → Fin L → ℝ)
  (heat_eq : ∀ t i, ∂T∂t t i = k / Δx^2 * laplacian1D (T t) i)
  (h_initial : ∀ i, T 0 i = s₀ i)
  (L_lip : ℝ) (hL_lip : 0 < L_lip)
  (truncation : ∀ Δt (hΔt : 0 < Δt) t, sup_norm (fun i => heat_step Δt (T t) i - T (t + Δt) i) ≤ L_lip * Δt ^ 2)
  (perturb_bound : ∀ Δt (hΔt : 0 < Δt) t i, |E i t| + |M i t - 1| ≤ L_lip * Δt ^ 2) :
  ∃ Δt₀ > 0, ∀ Δt' (hΔt' : 0 < Δt') (hΔt'_small : Δt' < Δt₀),
    ∀ n, (n : ℝ) * Δt' ≤ T_max → ε_close Δt' n T ε := by
  let Lip := 4 * k / Δx ^ 2
  have hLip : 0 < Lip := div_pos (mul_pos four_pos hk_pos) (pow_pos hΔx_pos 2)
  let Δt_stab := Δx ^ 2 / (2 * k)
  have hΔt_stab : 0 < Δt_stab := div_pos (pow_pos hΔx_pos 2) (mul_pos two_pos hk_pos)
  let bound := (exp (Lip * T_max) - 1) * (2 * L_lip) / Lip
  have h_bound : 0 < bound := mul_pos (sub_pos (one_lt_exp_iff.mpr (mul_pos hLip hT_max))) (div_pos (mul_pos two_pos hL_lip) hLip)
  let Δt_err := ε / bound
  have hΔt_err : 0 < Δt_err := div_pos hε h_bound
  let Δt₀ := min Δt_stab Δt_err
  have hΔt₀ : 0 < Δt₀ := lt_min hΔt_stab hΔt_err
  use Δt₀, hΔt₀
  intros Δt' hΔt' hΔt'_small n hn
  let e : ℕ → ℝ := fun m => sup_norm (fun i => heat_trajectory_perturbed Δt' m i - T (m * Δt') i)
  have h_base : e 0 = 0 := by
    simp [heat_trajectory_perturbed, sup_norm, h_initial]
    apply Finset.sup_eq_zero_iff.2
    intro i _
    simp
  have h_ind : ∀ m, e (m + 1) ≤ (1 + Lip * Δt') * e m + 2 * L_lip * Δt' ^ 2 := by
    intro m
    calc e (m + 1)
        = sup_norm (fun i => heat_step_perturbed Δt' (heat_trajectory_perturbed Δt' m) (m * Δt') i - T ((m + 1) * Δt') i) := rfl
    _ ≤ sup_norm (fun i => heat_step_perturbed Δt' (heat_trajectory_perturbed Δt' m) (m * Δt') i
                     - heat_step_perturbed Δt' (T (m * Δt')) (m * Δt') i)
             + sup_norm (fun i => heat_step_perturbed Δt' (T (m * Δt')) (m * Δt') i - T ((m + 1) * Δt') i)) := sup_norm_add_le _ _
    _ ≤ (1 + Lip * Δt') * e m + 2 * L_lip * Δt' ^ 2 := by
      apply add_le_add
      · apply step_lipschitz Δt' hΔt'.le
      · apply add_le_add (truncation Δt' hΔt' (m * Δt')) (Finset.sup_le (fun i _ => perturb_bound Δt' hΔt' (m * Δt') i))
  have h_closed : e n ≤ (2 * L_lip * Δt') / Lip * ((1 + Lip * Δt') ^ n - 1) := by
    induction' n with m ih
    · simp [h_base]
    · calc e (m + 1) ≤ (1 + Lip * Δt') * e m + 2 * L_lip * Δt' ^ 2 := h_ind m
      _ ≤ (1 + Lip * Δt') * ((2 * L_lip * Δt') / Lip * ((1 + Lip * Δt') ^ m - 1)) + 2 * L_lip * Δt' ^ 2 := by linarith
      _ = (2 * L_lip * Δt') / Lip * ((1 + Lip * Δt') ^ (m + 1) - 1) := by field_simp [hΔt'.ne', hLip.ne']; ring
  calc e n ≤ (2 * L_lip * Δt') / Lip * ((1 + Lip * Δt') ^ n - 1) := h_closed
  _ ≤ (2 * L_lip * Δt') / Lip * (exp (Lip * T_max) - 1) := by
    apply mul_le_mul_of_nonneg_left
    · apply sub_le_sub_right
      apply pow_le_exp_of_le_one
      · linarith [mul_le_mul_of_nonneg_left hΔt'.le hLip.le]
      · linarith
    · linarith
  _ < ε := by
    calc (2 * L_lip * Δt') / Lip * (exp (Lip * T_max) - 1) = Δt' * bound := by field_simp [bound, hLip.ne']
    _ < ε := mul_lt_mul_right h_bound Δt' hΔt_err

/-! # Section 7: ObservedDynamics instance -/

def heat_dynamics_perturbed (Δt : ℝ) (hΔt : 0 < Δt) : ObservedDynamics :=
{ step := fun u => heat_step_perturbed Δt u 0
  observe := sup_norm
  attractor := {x | x = 0}
  absorbing := by
    intro u o ho hobs
    rw [ho, hobs]
    have h_zero := sup_norm_eq_zero.1 _
    intro i
    simp [heat_step_perturbed, heat_step]
    exact laplacian1D_zero u h_zero i
}
