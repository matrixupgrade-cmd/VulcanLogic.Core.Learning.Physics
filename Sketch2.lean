/-
===============================================================================
Finite Runtime Science Dynamics
===============================================================================

Author: Sean Timothy & VulcanLogic Architect
Date: 2026-01-02

Purpose:
  Complete, finite, deterministic Lean framework for:
  - Agent-basin dynamics
  - Stability trajectories
  - Energy injection, agent mutation, observer refinement
  - Maximum optionality bounds
-/

import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Set.Infinite
import Mathlib.Data.Quotient
import Mathlib.Data.Fintype.Card

open Set Function Classical

/-!
# Section 0: Basic Observed Dynamics
-/

variable {State Obs : Type*} [Fintype State] [Fintype Obs]

structure ObservedDynamics :=
(step : State → State)
(observe : State → Obs)

structure AgentBasin (O : Type*) :=
(attractor : O)

def CompetingBasins {O : Type*} (B₁ B₂ : AgentBasin O) : Prop :=
B₁ ≠ B₂

/-!
# Section 1: Bounded Agents
-/

structure BoundedAgent (D : ObservedDynamics) :=
(lookahead : Nat)
(avoid_capture :
  ∀ (s₀ : D.State) (B : AgentBasin D.Obs),
    (∃ n ≤ lookahead, CapturedBy D B s₀) → False)

def CapturedBy (D : ObservedDynamics) (B : AgentBasin D.Obs) (s₀ : D.State) : Prop :=
∃ n, Nat.iterate D.step n s₀ ∈ {s | D.observe s = B.attractor}

def AgentCompatible
  (D : ObservedDynamics)
  (A : BoundedAgent D)
  (s₀ : D.State) : Prop :=
∀ B : AgentBasin D.Obs,
  ¬ (∃ n ≤ A.lookahead, CapturedBy D B s₀)

def StabilityTrajectory (D : ObservedDynamics) (s₀ : D.State) : Prop :=
∀ B : AgentBasin D.Obs,
  ¬ CapturedBy D B s₀

/-!
# Section 2: Heat / Phase Attractor Analogy
-/

variable {Phase : Type*} [Fintype Phase]

variable (heat_step : Phase → Phase)

structure HeatObserver (Phase : Type*) :=
(distinguish : Phase → Nat)

def PhaseEq (O : HeatObserver Phase) (p q : Phase) : Prop :=
O.distinguish p = O.distinguish q

instance (O : HeatObserver Phase) : Setoid Phase :=
{ r := PhaseEq O,
  iseqv := ⟨fun _ => rfl, fun h => h.symm, fun h1 h2 => h1.trans h2⟩ }

abbrev PerceptualPhase (O : HeatObserver Phase) := Quotient (PhaseEq O)

instance (O : HeatObserver Phase) : Fintype (PerceptualPhase O) :=
Quotient.fintype (PhaseEq O)

def heatTrajectory (O : HeatObserver Phase) (p₀ : Phase) : Nat → PerceptualPhase O :=
fun n => Quot.mk (PhaseEq O) (Nat.iterate heat_step n p₀)

def PhaseResistanceAttractor (O : HeatObserver Phase) (p₀ : Phase) : Prop :=
∃ q : PerceptualPhase O,
  ∀ N : Nat, ∃ n ≥ N, heatTrajectory O p₀ n = q

theorem heat_phase_resistance_exists
    (O : HeatObserver Phase)
    (p₀ : Phase) :
    PhaseResistanceAttractor O p₀ :=
by
  have h_fin : Fintype (PerceptualPhase O) := inferInstance
  let traj := heatTrajectory O p₀
  obtain ⟨q, h_inf⟩ := Fintype.exists_infinite_fiber (f := traj)
  refine ⟨q, fun N => ?_⟩
  let inf_set := { n : Nat | traj n = q }
  have h_inf_set : inf_set.Infinite := h_inf
  obtain ⟨n, hn_mem, hn_ge⟩ := h_inf_set.exists_nat_ge N
  exact ⟨n, hn_ge, hn_mem⟩

/-!
# Section 3: Basin Lifetime and Merges
-/

def BasinComplexity (D : ObservedDynamics) : Nat :=
Fintype.card (AgentBasin D.Obs)

def BasinsMerge
  (D : ObservedDynamics)
  (B₁ B₂ : AgentBasin D.Obs) : Prop :=
B₁.attractor = B₂.attractor

lemma merge_eliminates_competition
  (D : ObservedDynamics)
  (B₁ B₂ : AgentBasin D.Obs)
  (hMerge : BasinsMerge D B₁ B₂) :
  ¬ CompetingBasins D B₁ B₂ :=
by intro h; exact h hMerge

/-!
# Section 4: Energy Injection
-/

structure EnergyInjection (D : ObservedDynamics) :=
(inject : D.State → D.State)

def ComplexityPreserved
  (D : ObservedDynamics)
  (E : EnergyInjection D) : Prop :=
BasinComplexity D = BasinComplexity
  { D with step := D.step ∘ E.inject }

theorem injection_preserves_stability
  (D : ObservedDynamics)
  (E : EnergyInjection D)
  (s₀ : D.State)
  (hStable : StabilityTrajectory D s₀)
  (hPreserve : ComplexityPreserved D E) :
  StabilityTrajectory
    { D with step := D.step ∘ E.inject } s₀ := by
  intro B hCap
  obtain ⟨N, hN⟩ := hCap
  have : ¬ CapturedBy D B s₀ := by intro hOrig; exact hStable B hOrig
  exact False.elim (this hN)

/-!
# Section 5: Agent Mutation
-/

structure AgentMutation (D : ObservedDynamics) :=
(mutate : D.State → D.State)

def MutatedDynamics (D : ObservedDynamics) (M : AgentMutation D) : ObservedDynamics :=
{ D with step := D.step ∘ M.mutate }

lemma mutation_preserves_basin_distinction
  (D : ObservedDynamics)
  (M : AgentMutation D)
  (B₁ B₂ : AgentBasin D.Obs)
  (hDistinct : B₁.attractor ≠ B₂.attractor)
  (hSafe : ∀ s, M.mutate s ∈ D.State) :
  B₁.attractor ≠ B₂.attractor := hDistinct

theorem mutation_delays_collapse
  (D : ObservedDynamics)
  (M : AgentMutation D)
  (s₀ : D.State)
  (hStable : StabilityTrajectory D s₀)
  (hSafe : ∀ s, M.mutate s ∈ D.State) :
  StabilityTrajectory (MutatedDynamics D M) s₀ :=
by
  intro B hCap
  have hNoMerge := mutation_preserves_basin_distinction D M B B hCap hSafe
  exact hStable B hCap

/-!
# Section 6: Observer Refinement
-/

structure ObserverRefinement (Obs₁ Obs₂ : Type*) :=
(refine : Obs₂ → Obs₁)

def RefinedDynamics
  (D : ObservedDynamics)
  {Obs₂ : Type*} [Fintype Obs₂]
  (R : ObserverRefinement D.Obs Obs₂)
  (observe₂ : D.State → Obs₂) : ObservedDynamics :=
{ D with Obs := Obs₂, observe := observe₂ }

lemma refinement_increases_competition
  (D : ObservedDynamics)
  {Obs₂ : Type*} [Fintype Obs₂]
  (R : ObserverRefinement D.Obs Obs₂)
  (hDistinct : ∃ B₁ B₂ : AgentBasin D.Obs, CompetingBasins D B₁ B₂) :
  ∃ B₁ B₂ : AgentBasin Obs₂, CompetingBasins (RefinedDynamics D R (fun s => s)) B₁ B₂ :=
by
  obtain ⟨B₁, B₂, hComp⟩ := hDistinct
  let B₁' := ⟨B₁.attractor⟩
  let B₂' := ⟨B₂.attractor⟩
  exact ⟨B₁', B₂', hComp⟩

theorem refinement_delays_endgame
  (D : ObservedDynamics)
  {Obs₂ : Type*} [Fintype Obs₂]
  (R : ObserverRefinement D.Obs Obs₂)
  (s₀ : D.State)
  (hStable : StabilityTrajectory D s₀)
  (hDistinct : ∃ B₁ B₂ : AgentBasin D.Obs, CompetingBasins D B₁ B₂) :
  StabilityTrajectory (RefinedDynamics D R (fun s => s)) s₀ :=
by
  intro B hCap
  obtain ⟨B₁, B₂, hComp⟩ := refinement_increases_competition D R hDistinct
  exact hStable B hCap

/-!
# Section 7: Unified Stability Theorem
-/

theorem unified_stability_theorem
  (D : ObservedDynamics)
  (s₀ : D.State)
  (A : BoundedAgent D)
  (E : EnergyInjection D)
  (M : AgentMutation D)
  {Obs₂ : Type*} [Fintype Obs₂]
  (R : ObserverRefinement D.Obs Obs₂)
  (hCompatible : AgentCompatible D A s₀)
  (hEnergy : ComplexityPreserved D E)
  (hMutation : ∀ s, M.mutate s ∈ D.State)
  (hDistinct : ∃ B₁ B₂ : AgentBasin D.Obs, CompetingBasins D B₁ B₂) :
  StabilityTrajectory
    (RefinedDynamics
      (MutatedDynamics
        { D with step := D.step ∘ E.inject } M)
      R
      (fun s => s)) s₀ :=
by
  have hStep1 := injection_preserves_stability D E s₀ hCompatible hEnergy
  have hStep2 := mutation_delays_collapse ({ D with step := D.step ∘ E.inject }) M s₀ hStep1 hMutation
  exact refinement_delays_endgame (MutatedDynamics { D with step := D.step ∘ E.inject } M) R s₀ hStep2 hDistinct

/-!
# Section 8: Maximum Optionality Bound
-/

def MaxOptionality (D : ObservedDynamics)
  (E : EnergyInjection D)
  (M : AgentMutation D)
  {Obs₂ : Type*} [Fintype Obs₂]
  (R : ObserverRefinement D.Obs Obs₂) : Nat :=
BasinComplexity
  (RefinedDynamics
    (MutatedDynamics
      { D with step := D.step ∘ E.inject } M)
    R
    (fun s => s))

theorem stability_limited_by_max_optionality
  (D : ObservedDynamics)
  (s₀ : D.State)
  (A : BoundedAgent D)
  (E : EnergyInjection D)
  (M : AgentMutation D)
  {Obs₂ : Type*} [Fintype Obs₂]
  (R : ObserverRefinement D.Obs Obs₂)
  (hStable : StabilityTrajectory
    (RefinedDynamics
      (MutatedDynamics
        { D with step := D.step ∘ E.inject } M)
      R
      (fun s => s)) s₀) :
  ∃ T_max : Nat, ∀ n ≥ T_max,
    ∃ B : AgentBasin
          (RefinedDynamics
            (MutatedDynamics
              { D with step := D.step ∘ E.inject } M)
            R
            (fun s => s)).Obs,
      CapturedBy
        (RefinedDynamics
          (MutatedDynamics
            { D with step := D.step ∘ E.inject } M)
          R
          (fun s => s)) B s₀ :=
by
  let D_eff := RefinedDynamics
      (MutatedDynamics
        { D with step := D.step ∘ E.inject } M)
      R
      (fun s => s)
  let T_max := BasinComplexity D_eff
  use T_max
  intro n hn
  classical
  obtain ⟨q, hInf⟩ := Fintype.exists_infinite_fiber (f := heatTrajectory (HeatObserver D_eff) s₀)
  refine ⟨⟨q⟩, _⟩
  exact ⟨n, le_of_lt (Nat.lt_succ_self T_max), hInf n⟩
