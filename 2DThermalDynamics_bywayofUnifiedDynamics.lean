import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.NormedSpace.Basic
import Mathlib.Data.Set.Basic

open Classical
open Finset
open Real
open Nat

/-! # Section 0: Variables -/

variable {L W : ℕ} (hL : 2 < L) (hW : 2 < W)
variable (k Δx Δt : ℝ) (hk : 0 < k) (hΔx : 0 < Δx) (hΔt : 0 < Δt)
variable (s₀ : Fin L → Fin W → ℝ)
variable (E : Fin L → Fin W → ℝ → ℝ)
variable (M : Fin L → Fin W → ℝ → ℝ)

/-- 2D grid type -/
def Grid := Fin L → Fin W → ℝ

/-! # Section 1: Laplacian -/

/-- 2D Laplacian (5-point stencil, zero on boundaries) -/
def laplacian2D (u : Grid) (i : Fin L) (j : Fin W) : ℝ :=
  if i = 0 ∨ i = Fin.last (L - 1) ∨ j = 0 ∨ j = Fin.last (W - 1) then 0
  else u (i+1) j + u (i-1) j + u i (j+1) + u i (j-1) - 4 * u i j

/-! # Section 2: Sup norm -/

/-- Sup norm over 2D grid -/
def sup_norm2D (u : Grid) : ℝ :=
  (Finset.univ.product Finset.univ).sup (fun p => |u p.1 p.2|)

instance : Sup (Grid) := ⟨fun u v i j => max (u i j) (v i j)⟩

/-- Triangle inequality for sup norm -/
theorem sup_norm2D_triangle (u v : Grid) :
    sup_norm2D (u + v) ≤ sup_norm2D u + sup_norm2D v := by
  apply Finset.sup_le_iff.mpr
  rintro ⟨i, j⟩ _
  simp [Pi.add_apply]
  exact abs_add (u i j) (v i j) ▸
    add_le_add (le_sup (mem_product.mpr ⟨mem_univ i, mem_univ j⟩))
               (le_sup (mem_product.mpr ⟨mem_univ i, mem_univ j⟩))

/-! # Section 3: Heat steps -/

/-- Pure (unperturbed) 2D heat step -/
def heat_step2D (u : Grid) : Grid :=
  fun i j => u i j + k * Δt / Δx^2 * laplacian2D u i j

/-- Perturbed 2D heat step (additive + multiplicative) -/
def heat_step2D_perturbed (u : Grid) (t : ℝ) : Grid :=
  fun i j => heat_step2D u i j * M i j t + E i j t

/-! # Section 4: Trajectories -/

/-- Unperturbed trajectory over n time steps -/
def heat2D_trajectory (n : ℕ) : Grid :=
  Nat.iterate heat_step2D n s₀

/-- Perturbed trajectory over n time steps -/
def heat2D_trajectory_perturbed (n : ℕ) : Grid :=
  Nat.iterate (fun u m => heat_step2D_perturbed u (m * Δt)) n s₀

/-! # Section 5: Single-step perturbation bound -/

theorem heat_step2D_perturbation_bound
    (L_lip : ℝ)
    (hpert : ∀ i j t, |E i j t| + |M i j t - 1| ≤ L_lip * Δt^2)
    (u : Grid) (t : ℝ) :
    sup_norm2D (heat_step2D_perturbed u t - heat_step2D u) ≤ 2 * L_lip * Δt^2 := by
  apply Finset.sup_le_iff.mpr
  rintro ⟨i, j⟩ _
  simp [heat_step2D_perturbed, Pi.sub_apply]
  have h := hpert i j t
  calc
    |(heat_step2D u i j) * (M i j t - 1) + E i j t|
      ≤ |heat_step2D u i j| * |M i j t - 1| + |E i j t| := abs_add _ _
    _ ≤ ( |heat_step2D u i j| + 1 ) * |M i j t - 1| + |E i j t| := by
        rw [add_mul]; linarith [abs_nonneg (M i j t - 1)]
    _ ≤ |M i j t - 1| + |M i j t - 1| + |E i j t| := by
        linarith [le_trans (abs_abs _) (abs_le.mp (abs_nonneg _).le)]
    _ ≤ 2 * L_lip * Δt^2 := by linarith [h]

/-! # Section 6: ε-closeness -/

def ε_close2D (T : ℝ → Grid) (n : ℕ) (ε : ℝ) : Prop :=
  sup_norm2D (heat2D_trajectory_perturbed n - T (n * Δt)) < ε

/-! # Section 7: Constructive ε-limit theorem (discrete Grönwall) -/

theorem discrete_heat2D_perturbed_uniform_converges
    (T_max ε : ℝ) (hT_max : 0 < T_max) (hε : 0 < ε)
    (T : ℝ → Grid)
    (L_lip : ℝ) (hL_lip : 0 < L_lip)
    (truncation : ∀ Δt' (hΔt'_pos : 0 < Δt') t,
      sup_norm2D (heat_step2D (T t) - T (t + Δt')) ≤ L_lip * Δt'^2)
    (perturb_bound : ∀ Δt' (hΔt'_pos : 0 < Δt') t i j,
      |E i j t| + |M i j t - 1| ≤ L_lip * Δt'^2)
    :
    ∃ Δt₀ > 0, ∀ Δt' (hΔt'_pos : 0 < Δt') (hΔt'_small : Δt' < Δt₀)
      (n : ℕ) (hn : (n : ℝ) * Δt' ≤ T_max),
      ε_close2D T n ε := by
  -- Lipschitz constant of the explicit heat operator in sup-norm
  let Lip := 8 * k / Δx^2
  have hLip : 0 < Lip := by
    apply div_pos
    · exact mul_pos (by linarith [hk]) (by linarith)
    · exact pow_pos hΔx 2

  -- Grönwall amplification factor
  let K := Real.exp (Lip * T_max)
  have hK : 1 < K := one_lt_exp_iff.mpr (mul_pos hLip hT_max)

  let bound := (K - 1) * 2 * L_lip / Lip
  have hbound : 0 < bound := mul_pos (sub_pos.mpr hK) (mul_pos (by linarith) (div_pos (by linarith [hL_lip]) hLip))

  let Δt₀ := ε / bound
  have hΔt₀ : 0 < Δt₀ := div_pos hε hbound

  use Δt₀, hΔt₀
  intros Δt' hΔt' hsmall n hn_time

  -- Error at step m
  let e : ℕ → ℝ := fun m =>
    sup_norm2D (Nat.iterate (fun u _ => heat_step2D_perturbed u (m * Δt')) m s₀ - T (m * Δt'))

  -- Base case
  have e0 : e 0 = 0 := by simp [e, Nat.iterate_zero, sup_norm2D]

  -- Inductive step: error growth
  have step : ∀ m, e (m + 1) ≤ (1 + Lip * Δt') * e m + 2 * L_lip * Δt'^2 := by
    intro m
    rw [e, Nat.iterate_succ']
    calc
      sup_norm2D (heat_step2D_perturbed (Nat.iterate _ m s₀) (m * Δt') - T ((m + 1) * Δt'))
        ≤ sup_norm2D (heat_step2D_perturbed (Nat.iterate _ m s₀) (m * Δt') - heat_step2D (T (m * Δt')))
          + sup_norm2D (heat_step2D (T (m * Δt')) - T ((m + 1) * Δt')) := sup_norm2D_triangle _ _
      _ ≤ 2 * L_lip * Δt'^2 + L_lip * Δt'^2 :=
            add_le_add
              (heat_step2D_perturbation_bound L_lip (perturb_bound Δt' hΔt' (m * Δt')) _ _)
              (truncation Δt' hΔt' (m * Δt'))
      _ ≤ (1 + Lip * Δt') * e m + 2 * L_lip * Δt'^2 := by
            have : 3 * L_lip * Δt'^2 ≤ (1 + Lip * Δt') * e m + 2 * L_lip * Δt'^2 := by linarith
            exact this

  -- Discrete Grönwall inequality
  have gronwall : e n ≤ 2 * L_lip / Lip * ((1 + Lip * Δt')^n - 1) * Δt' := by
    induction' n using Nat.strongInductionOn with n ih
    · simp [e0]
    · rw [e]
      calc
        e (n + 1) ≤ (1 + Lip * Δt') * e n + 2 * L_lip * Δt'^2 := step n
        _ ≤ (1 + Lip * Δt') * (2 * L_lip / Lip * ((1 + Lip * Δt')^n - 1) * Δt') + 2 * L_lip * Δt'^2 :=
              by linarith [ih n (lt_add_one n)]
        _ = 2 * L_lip / Lip * ((1 + Lip * Δt')^(n + 1) - 1) * Δt' := by
              ring_nf; rw [mul_add, mul_comm Δt' _, ← mul_assoc]; ring

  -- Bound the geometric factor by the exponential
  have geom_exp : (1 + Lip * Δt')^(n : ℝ) ≤ Real.exp (Lip * (n * Δt')) := by
    apply Real.exp_bound_one_add
    exact mul_nonneg hLip.le hΔt'.le

  have final : e n ≤ bound * Δt' := calc
    e n ≤ 2 * L_lip / Lip * ((1 + Lip * Δt')^n - 1) * Δt' := gronwall
    _ ≤ 2 * L_lip / Lip * (Real.exp (Lip * (n * Δt')) - 1) * Δt' := by
          apply mul_le_mul_of_nonneg_left _ (by linarith)
          apply sub_le_sub le_rfl geom_exp
    _ ≤ 2 * L_lip / Lip * (Real.exp (Lip * T_max) - 1) * Δt' := by
          apply mul_le_mul_of_nonneg_left _ (by linarith)
          apply sub_le_sub le_rfl
          apply Real.exp_monotone
          apply mul_le_mul_of_nonneg_left hn_time hLip.le
    _ = bound * Δt' := rfl

  calc
    sup_norm2D (heat2D_trajectory_perturbed n - T (n * Δt)) = e n := rfl
    _ ≤ bound * Δt' := final
    _ < bound * Δt₀ := mul_lt_mul_of_pos_left hsmall hbound
    _ = ε := by field_simp [Δt₀, hbound.ne']

/-! # Section 8: ObservedDynamics instance -/

structure ObservedDynamics where
  step      : Grid → Grid
  observe   : Grid → ℝ
  attractor : Set Grid
  absorbing : ∀ u, u ∈ attractor → observe u = 0 → ∀ i j, laplacian2D u i j = 0

def heat_dynamics2D_perturbed_inst : ObservedDynamics :=
{ step := fun u => heat_step2D_perturbed u 0
  , observe := sup_norm2D
  , attractor := {fun _ _ => (0 : ℝ)}
  , absorbing := by
    rintro u ⟨rfl⟩ hobs i j
    have hne : (univ.product univ).Nonempty := product_nonempty univ_nonempty univ_nonempty
    rw [sup_norm2D, Finset.sup_const hne] at hobs
    split_ifs at hobs with h <;> simp_all
    simp [laplacian2D]
}
