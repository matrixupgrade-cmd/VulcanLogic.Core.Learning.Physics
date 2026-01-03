import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Analysis.SpecialFunctions.ExpLog -- Better for exp bounds
import Mathlib.Analysis.NormedSpace.Basic
import Mathlib.Data.Set.Basic

open Classical
open Finset
open Real
open Nat

/-! # Section 0: Variables -/

variable {L W H : ℕ} (hL : 2 < L) (hW : 2 < W) (hH : 2 < H)
variable (k Δx Δt : ℝ) (hk : 0 < k) (hΔx : 0 < Δx) (hΔt : 0 < Δt)
variable (s₀ : Fin L → Fin W → Fin H → ℝ)
variable (E : Fin L → Fin W → Fin H → ℝ → ℝ)
variable (M : Fin L → Fin W → Fin H → ℝ → ℝ)

/-- 3D grid type -/
def Grid3D := Fin L → Fin W → Fin H → ℝ

/-! # Section 1: Laplacian -/

/-- 3D Laplacian (7-point stencil, zero on boundaries) -/
def laplacian3D (u : Grid3D) (i : Fin L) (j : Fin W) (k' : Fin H) : ℝ :=
  if i = 0 ∨ i = Fin.last (L - 1)
     ∨ j = 0 ∨ j = Fin.last (W - 1)
     ∨ k' = 0 ∨ k' = Fin.last (H - 1) then 0
  else u (i+1) j k' + u (i-1) j k' +
       u i (j+1) k' + u i (j-1) k' +
       u i j (k'+1) + u i j (k'-1) -
       6 * u i j k'

/-! # Section 2: Sup norm -/

/-- Sup norm over 3D grid -/
def sup_norm3D (u : Grid3D) : ℝ :=
  (univ.product (univ.product univ)).sup (fun p => |u p.1 p.2.1 p.2.2|)

instance : Sup (Grid3D) := ⟨fun u v i j k' => max (u i j k') (v i j k')⟩

/-- Triangle inequality for sup norm -/
theorem sup_norm3D_triangle (u v : Grid3D) :
    sup_norm3D (u + v) ≤ sup_norm3D u + sup_norm3D v := by
  apply Finset.sup_le_iff.mpr
  rintro ⟨⟨i, j⟩, k'⟩ _
  simp only [Pi.add_apply]
  apply (abs_add (u i j k') (v i j k')).le
  apply add_le_add
  · apply le_sup
    exact mem_product.mpr ⟨mem_product.mpr ⟨mem_univ _, mem_univ _⟩, mem_univ _⟩
  · apply le_sup
    exact mem_product.mpr ⟨mem_product.mpr ⟨mem_univ _, mem_univ _⟩, mem_univ _⟩

/-! # Section 3: Heat steps -/

/-- Pure 3D heat step -/
def heat_step3D (u : Grid3D) : Grid3D :=
  fun i j k' => u i j k' + k * Δt / Δx^2 * laplacian3D u i j k'

/-- Perturbed 3D heat step -/
def heat_step3D_perturbed (u : Grid3D) (t : ℝ) : Grid3D :=
  fun i j k' => heat_step3D u i j k' * M i j k' t + E i j k' t

/-! # Section 4: Trajectories -/

/-- Unperturbed trajectory -/
def heat3D_trajectory (n : ℕ) : Grid3D :=
  Nat.iterate heat_step3D n s₀

/-- Perturbed trajectory -/
def heat3D_trajectory_perturbed (n : ℕ) : Grid3D :=
  Nat.iterate (fun u m => heat_step3D_perturbed u (m * Δt)) n s₀

/-! # Section 5: Single-step perturbation bound -/

theorem heat_step3D_perturbation_bound
    (L_lip : ℝ)
    (hpert : ∀ i j k' t, |E i j k' t| + |M i j k' t - 1| ≤ L_lip * Δt^2)
    (u : Grid3D) (t : ℝ) :
    sup_norm3D (heat_step3D_perturbed u t - heat_step3D u) ≤ 2 * L_lip * Δt^2 := by
  apply Finset.sup_le_iff.mpr
  rintro ⟨⟨i, j⟩, k'⟩ _
  simp [heat_step3D_perturbed, Pi.sub_apply]
  have h := hpert i j k' t
  calc
    |(heat_step3D u i j k') * (M i j k' t - 1) + E i j k' t|
      ≤ |heat_step3D u i j k'| * |M i j k' t - 1| + |E i j k' t| := abs_add _ _
    _ ≤ (|heat_step3D u i j k'| + 1) * |M i j k' t - 1| + |E i j k' t| :=
        by rw [add_mul]; linarith [abs_nonneg (M i j k' t - 1)]
    _ ≤ |M i j k' t - 1| + |M i j k' t - 1| + |E i j k' t| :=
        by linarith [abs_le.1 (abs_abs (heat_step3D u i j k')).le]
    _ ≤ 2 * L_lip * Δt^2 := by linarith [h]

/-! # Section 6: ε-closeness -/

def ε_close3D (T : ℝ → Grid3D) (n : ℕ) (ε : ℝ) : Prop :=
  sup_norm3D (heat3D_trajectory_perturbed n - T (n * Δt)) < ε

/-! # Section 7: Constructive ε-limit theorem -/

theorem discrete_heat3D_perturbed_uniform_converges
    (T_max ε : ℝ) (hT_max : 0 < T_max) (hε : 0 < ε)
    (T : ℝ → Grid3D)
    (L_lip : ℝ) (hL_lip : 0 < L_lip)
    (truncation : ∀ Δt' (hΔt'_pos : 0 < Δt') t,
      sup_norm3D (heat_step3D (T t) - T (t + Δt')) ≤ L_lip * Δt'^2)
    (perturb_bound : ∀ Δt' (hΔt'_pos : 0 < Δt') t i j k',
      |E i j k' t| + |M i j k' t - 1| ≤ L_lip * Δt'^2)
    :
    ∃ Δt₀ > 0, ∀ Δt' (hΔt'_pos : 0 < Δt') (hΔt'_small : Δt' < Δt₀)
      (n : ℕ) (hn : (n : ℝ) * Δt' ≤ T_max),
      ε_close3D T n ε := by
  -- Lipschitz constant for explicit 3D heat scheme in sup norm
  let Lip := 12 * k / Δx^2
  have hLip : 0 < Lip := by
    apply div_pos (mul_pos (by linarith [hk]) (by linarith)) (pow_pos hΔx 2)

  let K := Real.exp (Lip * T_max)
  have hK_gt1 : 1 < K := exp_one_lt hLip hT_max

  let bound := (K - 1) * 2 * L_lip / Lip
  have hbound : 0 < bound := mul_pos (sub_pos.mpr hK_gt1) (div_pos (mul_pos (by linarith) hL_lip) hLip)

  let Δt₀ := ε / bound
  have hΔt₀ : 0 < Δt₀ := div_pos hε hbound

  use Δt₀, hΔt₀
  intros Δt' hΔt'_pos hsmall n hn_time

  -- Error at step m
  let e : ℕ → ℝ := fun m =>
    sup_norm3D (Nat.iterate (fun u _ => heat_step3D_perturbed u (m * Δt')) m s₀ - T (m * Δt'))

  have e0 : e 0 = 0 := by simp [e, Nat.iterate_zero, sup_norm3D]

  -- One-step error growth
  have step : ∀ m, e (m + 1) ≤ (1 + Lip * Δt') * e m + 2 * L_lip * Δt'^2 := by
    intro m
    rw [e, Nat.iterate_succ']
    exact calc
      sup_norm3D (heat_step3D_perturbed _ (m * Δt') - T ((m + 1) * Δt'))
        ≤ sup_norm3D (heat_step3D_perturbed _ (m * Δt') - heat_step3D (T (m * Δt')))
          + sup_norm3D (heat_step3D (T (m * Δt')) - T ((m + 1) * Δt')) :=
            sup_norm3D_triangle _ _
      _ ≤ 2 * L_lip * Δt'^2 + L_lip * Δt'^2 :=
            add_le_add
              (heat_step3D_perturbation_bound L_lip (perturb_bound Δt' hΔt'_pos (m * Δt')) _ _)
              (truncation Δt' hΔt'_pos (m * Δt'))
      _ ≤ (1 + Lip * Δt') * e m + 2 * L_lip * Δt'^2 := by
            have : 3 * L_lip * Δt'^2 ≤ (1 + Lip * Δt') * e m + 2 * L_lip * Δt'^2 := by linarith
            exact this

  -- Discrete Grönwall inequality
  have gronwall : ∀ n, e n ≤ 2 * L_lip / Lip * ((1 + Lip * Δt')^n - 1) * Δt' := by
    intro n
    induction' n using Nat.strongInductionOn with n ih
    · simp [e0]
    · calc
        e (n + 1) ≤ (1 + Lip * Δt') * e n + 2 * L_lip * Δt'^2 := step n
        _ ≤ (1 + Lip * Δt') * (2 * L_lip / Lip * ((1 + Lip * Δt')^n - 1) * Δt') + 2 * L_lip * Δt'^2 :=
              by linarith [ih n (Nat.lt_succ_self n)]
        _ = 2 * L_lip / Lip * ((1 + Lip * Δt')^(n + 1) - 1) * Δt' := by
              ring_nf; rw [mul_add, ← mul_assoc]; ring

  -- Bound geometric term by exponential
  have geom_exp : (1 + Lip * Δt')^(n : ℝ) ≤ Real.exp (Lip * (n * Δt')) := by
    apply Real.exp_bound_one_add (r := Lip * Δt')
    exact mul_nonneg hLip.le hΔt'_pos.le

  have final : e n ≤ bound * Δt' := calc
    e n ≤ 2 * L_lip / Lip * ((1 + Lip * Δt')^n - 1) * Δt' := gronwall n
    _ ≤ 2 * L_lip / Lip * (Real.exp (Lip * (n * Δt')) - 1) * Δt' := by
          apply mul_le_mul_of_nonneg_left _ (by linarith)
          apply sub_le_sub le_rfl geom_exp
    _ ≤ 2 * L_lip / Lip * (Real.exp (Lip * T_max) - 1) * Δt' := by
          apply mul_le_mul_of_nonneg_left _ (by linarith)
          apply sub_le_sub le_rfl
          apply Real.exp_monotone
          exact mul_le_mul_of_nonneg_left hn_time hLip.le
    _ = bound * Δt' := rfl

  calc
    sup_norm3D (heat3D_trajectory_perturbed n - T (n * Δt)) = e n := rfl
    _ ≤ bound * Δt' := final
    _ < bound * Δt₀ := mul_lt_mul_of_pos_left hsmall hbound
    _ = ε := by field_simp [Δt₀, bound]

/-! # Section 8: ObservedDynamics instance -/

structure ObservedDynamics3D where
  step      : Grid3D → Grid3D
  observe   : Grid3D → ℝ
  attractor : Set Grid3D
  absorbing : ∀ u, u ∈ attractor → observe u = 0 → ∀ i j k', laplacian3D u i j k' = 0

def heat_dynamics3D_perturbed_inst : ObservedDynamics3D :=
{ step := fun u => heat_step3D_perturbed u 0
  , observe := sup_norm3D
  , attractor := {fun _ _ _ => (0 : ℝ)}
  , absorbing := by
    rintro u ⟨rfl⟩ hobs i j k'
    have hne : (univ.product (univ.product univ)).Nonempty :=
      product_nonempty univ_nonempty (product_nonempty univ_nonempty univ_nonempty)
    rw [sup_norm3D, Finset.sup_const hne] at hobs
    split_ifs at hobs <;> simp_all
    simp [laplacian3D]
}
