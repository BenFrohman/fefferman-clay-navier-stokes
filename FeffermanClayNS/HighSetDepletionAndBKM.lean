/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

module

public import FeffermanClayNS.TorusStrainExclusion

open scoped BigOperators Gradient Topology
open ENNReal InnerProductSpace MeasureTheory Finset Filter
open NavierStokes3D

/-!
# Conditional Reduction of Fefferman's Periodic Problem (B) via High-Set Direction Depletion & BKM

This module formalizes the **conditional** analytic reduction chain on `𝕋³ = ℝ³ / ℤ³`:

1. **Pointwise Maximum-Vorticity Rate Reduction (`unmodified_max_rate_of_cubic_source`,
   `viscous_direction_dissipation_bridge`, `scale_invariant_cubic_rate_of_direction_coercivity`):**
   At a spatial maximum `x_t` where `M = ‖ω(t, x_t)‖ > 0` and `(u · ∇)‖ω‖²(x_t) = 0`, dividing the
   unmodified vorticity norm-squared identity by `2 M` reduces the time-derivative bound for `M(t)`
   to the sum of vortex stretching `⟨ω, (ω · ∇) u⟩` and viscous dissipation `ν ⟨ω, Δω⟩`.
   When viscous direction-gradient dissipation `-ν M² ‖∇ξ‖²` satisfies a high-vorticity coercivity
   estimate on `𝕋³`, it yields a cubic comparison differential inequality.

2. **Cubic Comparison ODE Ceiling (`comparison_ode_ceiling`):**
   Unconditional proof (via `image_le_of_deriv_right_lt_deriv_boundary`) that any differentiable
   trajectory `M : ℝ → ℝ` on `[0, T]` satisfying `deriv M t ≤ C_CZ * M(t)² - κ'' * M(t)³` with
   `C_CZ > 0` and `κ'' > 0` is uniformly bounded by `Y = max (M 0) (C_CZ / κ'')`.

3. **Explicit Conditional Reductions to `Clay_B_exact` (`clay_B_exact_of_periodic_tether_bound`,
   `clay_B_exact_of_torus_direction_depletion`):**
   These theorems are **CONDITIONAL reductions**. Their hypotheses (`PeriodicDirectionDepletionBound ν`,
   `PeriodicTetherClosingBound ν`, and `PeriodicBKMContinuation ν`) are stated explicitly as
   hypotheses in the theorem signatures, never as axioms. Establishing `PeriodicDirectionDepletionBound ν`
   (or `PeriodicTetherClosingBound ν`) for arbitrary smooth `ℤ³`-periodic initial data remains OPEN.
-/

namespace FeffermanClayNS

/-- **Pointwise Unmodified Maximum-Vorticity Rate Reduction (`unmodified_max_rate_of_cubic_source`):**
If `M > 0`, `M' ≤ (⟨ω, (ω · ∇) u⟩ - (u · ∇)‖ω‖² / 2 + ν ⟨ω, Δω⟩) / M`, the convective transport
of `‖ω‖²` vanishes at the spatial maximum (`hconv_max : conv_norm_sq = 0`), and the net source
satisfies `stretching + ν * visc_lap ≤ C_CZ * M ^ 3 - κ'' * M ^ 4`, then
`M' ≤ C_CZ * M ^ 2 - κ'' * M ^ 3`. -/
public theorem unmodified_max_rate_of_cubic_source
    (M M' stretching conv_norm_sq ν visc_lap C_CZ κ'' : ℝ)
    (hM_pos : 0 < M)
    (h_unmod_id : M' ≤ (stretching - conv_norm_sq / 2 + ν * visc_lap) / M)
    (hconv_max : conv_norm_sq = 0)
    (h_source : stretching + ν * visc_lap ≤ C_CZ * M ^ 3 - κ'' * M ^ 4) :
    M' ≤ C_CZ * M ^ 2 - κ'' * M ^ 3 := by
  have h1 : stretching - conv_norm_sq / 2 + ν * visc_lap ≤ C_CZ * M ^ 3 - κ'' * M ^ 4 := by
    rw [hconv_max]
    linarith
  have h2 : (stretching - conv_norm_sq / 2 + ν * visc_lap) / M ≤
      (C_CZ * M ^ 3 - κ'' * M ^ 4) / M :=
    div_le_div_of_nonneg_right h1 (le_of_lt hM_pos)
  have hM_ne : M ≠ 0 := ne_of_gt hM_pos
  have h3 : (C_CZ * M ^ 3 - κ'' * M ^ 4) / M = C_CZ * M ^ 2 - κ'' * M ^ 3 := by
    field_simp [hM_ne]
  linarith

/-- **Viscous Direction-Gradient Dissipation Bridge (`viscous_direction_dissipation_bridge`):**
At a spatial maximum `M > 0` where `conv_norm_sq = 0`, if vortex stretching satisfies
`stretching ≤ C_CZ * M ^ 3`, viscous dissipation satisfies the direction-gradient decomposition
`ν * visc_lap ≤ -ν * M ^ 2 * grad_xi_sq`, and the high-vorticity direction gradient satisfies
`ν * grad_xi_sq ≥ κ'' * M ^ 2`, then `M' ≤ C_CZ * M ^ 2 - κ'' * M ^ 3`. -/
public theorem viscous_direction_dissipation_bridge
    (M M' stretching conv_norm_sq ν visc_lap grad_xi_sq C_CZ κ'' : ℝ)
    (hM_pos : 0 < M)
    (h_unmod_id : M' ≤ (stretching - conv_norm_sq / 2 + ν * visc_lap) / M)
    (hconv_max : conv_norm_sq = 0)
    (h_stretch : stretching ≤ C_CZ * M ^ 3)
    (h_visc_decomp : ν * visc_lap ≤ -(ν * M ^ 2 * grad_xi_sq))
    (h_dir_coercive : κ'' * M ^ 2 ≤ ν * grad_xi_sq) :
    M' ≤ C_CZ * M ^ 2 - κ'' * M ^ 3 := by
  have hM2_nonneg : 0 ≤ M ^ 2 := sq_nonneg M
  have h_dissip : κ'' * M ^ 4 ≤ ν * M ^ 2 * grad_xi_sq := by
    calc
      κ'' * M ^ 4 = M ^ 2 * (κ'' * M ^ 2) := by ring
      _ ≤ M ^ 2 * (ν * grad_xi_sq) := mul_le_mul_of_nonneg_left h_dir_coercive hM2_nonneg
      _ = ν * M ^ 2 * grad_xi_sq := by ring
  have h_source : stretching + ν * visc_lap ≤ C_CZ * M ^ 3 - κ'' * M ^ 4 := by
    linarith
  exact unmodified_max_rate_of_cubic_source M M' stretching conv_norm_sq ν visc_lap C_CZ κ''
    hM_pos h_unmod_id hconv_max h_source

/-- **Scale-Invariant Cubic Rate under `λ⁶` Direction Coercivity (`scale_invariant_cubic_rate_of_direction_coercivity`):**
When the viscous direction-gradient dissipation satisfies the scale-invariant `λ⁶`-homogeneous
bound `ν * grad_xi_sq ≥ κ_eff * M` (so `ν * M ^ 2 * grad_xi_sq ≥ κ_eff * M ^ 3`), both the
stretching bound `C_CZ * M ^ 3` and the viscous direction dissipation `-κ_eff * M ^ 3` have
cubic degree in `M` (`λ⁶` under Navier–Stokes rescaling), yielding `M' ≤ (C_CZ - κ_eff) * M ^ 2`. -/
public theorem scale_invariant_cubic_rate_of_direction_coercivity
    (M M' stretching conv_norm_sq ν visc_lap grad_xi_sq C_CZ κ_eff : ℝ)
    (hM_pos : 0 < M)
    (h_unmod_id : M' ≤ (stretching - conv_norm_sq / 2 + ν * visc_lap) / M)
    (hconv_max : conv_norm_sq = 0)
    (h_stretch : stretching ≤ C_CZ * M ^ 3)
    (h_visc_decomp : ν * visc_lap ≤ -(ν * M ^ 2 * grad_xi_sq))
    (h_scale_coercive : κ_eff * M ≤ ν * grad_xi_sq) :
    M' ≤ (C_CZ - κ_eff) * M ^ 2 := by
  have hM2_nonneg : 0 ≤ M ^ 2 := sq_nonneg M
  have h_dissip : κ_eff * M ^ 3 ≤ ν * M ^ 2 * grad_xi_sq := by
    calc
      κ_eff * M ^ 3 = M ^ 2 * (κ_eff * M) := by ring
      _ ≤ M ^ 2 * (ν * grad_xi_sq) := mul_le_mul_of_nonneg_left h_scale_coercive hM2_nonneg
      _ = ν * M ^ 2 * grad_xi_sq := by ring
  have h1 : stretching - conv_norm_sq / 2 + ν * visc_lap ≤ (C_CZ - κ_eff) * M ^ 3 := by
    rw [hconv_max]
    linarith
  have h2 : (stretching - conv_norm_sq / 2 + ν * visc_lap) / M ≤
      ((C_CZ - κ_eff) * M ^ 3) / M :=
    div_le_div_of_nonneg_right h1 (le_of_lt hM_pos)
  have hM_ne : M ≠ 0 := ne_of_gt hM_pos
  have h3 : ((C_CZ - κ_eff) * M ^ 3) / M = (C_CZ - κ_eff) * M ^ 2 := by
    field_simp [hM_ne]
  linarith

/-- Factorization of the cubic comparison vector field `C_CZ * z² - κ'' * z³ = z² * (C_CZ - κ'' * z)`. -/
public theorem cubic_comparison_field_eq (C_CZ κ'' z : ℝ) :
    C_CZ * z ^ 2 - κ'' * z ^ 3 = z ^ 2 * (C_CZ - κ'' * z) := by
  ring

/-- Strictly above the threshold `C_CZ / κ''`, the cubic comparison vector field is negative. -/
public theorem cubic_comparison_field_neg_of_gt
    {C_CZ κ'' z : ℝ} (hC : 0 < C_CZ) (hκ : 0 < κ'') (hz : C_CZ / κ'' < z) :
    C_CZ * z ^ 2 - κ'' * z ^ 3 < 0 := by
  have hzpos : 0 < z := lt_trans (div_pos hC hκ) hz
  have hz2 : 0 < z ^ 2 := sq_pos_of_pos hzpos
  have hlin : C_CZ - κ'' * z < 0 := by
    have hmul : κ'' * (C_CZ / κ'') < κ'' * z := mul_lt_mul_of_pos_left hz hκ
    rw [mul_div_cancel₀ C_CZ (ne_of_gt hκ)] at hmul
    linarith [hmul]
  rw [cubic_comparison_field_eq]
  exact mul_neg_of_pos_of_neg hz2 hlin

/-- **Cubic Comparison ODE Stability Ceiling (`comparison_ode_ceiling`):**
For any differentiable trajectory `M : ℝ → ℝ` on `[0, T]` satisfying the cubic differential
inequality `deriv M t ≤ C_CZ * (M t)² - κ'' * (M t)³` with `C_CZ > 0` and `κ'' > 0`,
`M t ≤ max (M 0) (C_CZ / κ'')` for every `t ∈ [0, T]`. -/
public theorem comparison_ode_ceiling
    (M : ℝ → ℝ) (T C_CZ κ'' : ℝ)
    (hC_pos : 0 < C_CZ) (hκ_pos : 0 < κ'')
    (hM_diff : ∀ t ∈ Set.Icc (0 : ℝ) T, DifferentiableAt ℝ M t)
    (hODE : ∀ t ∈ Set.Icc (0 : ℝ) T, deriv M t ≤ C_CZ * (M t) ^ 2 - κ'' * (M t) ^ 3) :
    ∀ t ∈ Set.Icc (0 : ℝ) T, M t ≤ max (M 0) (C_CZ / κ'') := by
  intro t ht
  set Y := max (M 0) (C_CZ / κ'')
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hbarrier : C_CZ / κ'' < Y + ε :=
    lt_of_le_of_lt (le_max_right (M 0) (C_CZ / κ'')) (lt_add_of_pos_right _ hε)
  have hM0 : M 0 ≤ Y + ε :=
    (le_max_left (M 0) (C_CZ / κ'')).trans (le_add_of_nonneg_right hε.le)
  have hMC : ContinuousOn M (Set.Icc (0 : ℝ) t) := fun x hx =>
    (hM_diff x ⟨hx.1, le_trans hx.2 ht.2⟩).continuousAt.continuousWithinAt
  have hMW : ∀ x ∈ Set.Ico (0 : ℝ) t,
      HasDerivWithinAt M (deriv M x) (Set.Ici x) x := fun x hx =>
    (hM_diff x ⟨hx.1, le_trans (le_of_lt hx.2) ht.2⟩).hasDerivAt.hasDerivWithinAt
  have hB : ∀ x, HasDerivAt (fun _ : ℝ => Y + ε) (0 : ℝ) x := fun x =>
    hasDerivAt_const x (Y + ε)
  have hcontact : ∀ x ∈ Set.Ico (0 : ℝ) t, M x = Y + ε → deriv M x < 0 := by
    intro x hx hxeq
    have hneg : C_CZ * (Y + ε) ^ 2 - κ'' * (Y + ε) ^ 3 < 0 :=
      cubic_comparison_field_neg_of_gt hC_pos hκ_pos hbarrier
    have hdot := hODE x ⟨hx.1, le_trans (le_of_lt hx.2) ht.2⟩
    rw [hxeq] at hdot
    linarith
  have hle :=
    image_le_of_deriv_right_lt_deriv_boundary (f := M) (f' := deriv M)
      (a := 0) (b := t) (B := fun _ => Y + ε) (B' := fun _ => (0 : ℝ))
      hMC hMW hM0 hB hcontact
  exact hle ⟨ht.1, le_rfl⟩

/-! ## Conditional Periodic Hypotheses & Conditional Reductions to `Clay_B_exact`

**Honesty & Scope Notice:**
Both `PeriodicDirectionDepletionBound ν` and `PeriodicTetherClosingBound ν` below are **OPEN**
analytic hypotheses on the periodic 3-torus `𝕋³ = ℝ³ / ℤ³`. They are defined as `Prop`s and
passed explicitly as hypotheses to the conditional reduction theorems
`clay_B_exact_of_periodic_tether_bound` and `clay_B_exact_of_torus_direction_depletion`. -/

/-- **Conditional Hypothesis 1a (`PeriodicDirectionDepletionBound` — OPEN):**
For every smooth, divergence-free, `ℤ³`-periodic initial datum `u₀`, there exist positive
constants `C_CZ, κ'' > 0` such that along any local-in-time periodic smooth solution `(u, p)` on
`[0, T] × (ℝ³ / ℤ³)`, the spatial supremum of vorticity `M(t) = ‖ω(t)‖_∞` is differentiable on
`[0, T]` and obeys the cubic direction-depletion differential inequality
`deriv M t ≤ C_CZ * M(t)² - κ'' * M(t)³`. -/
@[expose] public def PeriodicDirectionDepletionBound (ν : ℝ) : Prop :=
  ∀ u₀ : VelocityField,
    IsPeriodicSmoothInitialData u₀ →
    ∃ C_CZ κ'' : ℝ, 0 < C_CZ ∧ 0 < κ'' ∧
      ∀ (T : ℝ) (u : TimeDependentVelocity) (p : TimeDependentPressure),
        IsPeriodicSmoothSolutionOn ν u₀ (fun _ _ => 0) T u p →
        (∀ t ∈ Set.Icc (0 : ℝ) T,
          DifferentiableAt ℝ (fun s => vorticity_sup_norm (vorticity (u s))) t) ∧
        (∀ t ∈ Set.Icc (0 : ℝ) T,
          deriv (fun s => vorticity_sup_norm (vorticity (u s))) t ≤
            C_CZ * (vorticity_sup_norm (vorticity (u t))) ^ 2 -
              κ'' * (vorticity_sup_norm (vorticity (u t))) ^ 3)

/-- **Conditional Hypothesis 1b (`PeriodicTetherClosingBound` / Uniform Periodic Vorticity Ceiling — OPEN):**
For every smooth, divergence-free, `ℤ³`-periodic initial datum `u₀`, there exists a finite ceiling
`Y ≥ 0` (depending only on `u₀` and `ν`) that bounds `‖ω(t)‖_∞` uniformly along any local-in-time
periodic smooth solution `(u, p)` on `[0, T] × (ℝ³ / ℤ³)`. -/
@[expose] public def PeriodicTetherClosingBound (ν : ℝ) : Prop :=
  ∀ u₀ : VelocityField,
    IsPeriodicSmoothInitialData u₀ →
    ∃ Y : ℝ, 0 ≤ Y ∧
      ∀ (T : ℝ) (u : TimeDependentVelocity) (p : TimeDependentPressure),
        IsPeriodicSmoothSolutionOn ν u₀ (fun _ _ => 0) T u p →
        ∀ t ∈ Set.Icc (0 : ℝ) T,
          vorticity_sup_norm (vorticity (u t)) ≤ Y

/-- Alias for `PeriodicTetherClosingBound` using purely classical PDE terminology. -/
@[expose] public abbrev PeriodicUniformVorticityCeiling (ν : ℝ) : Prop :=
  PeriodicTetherClosingBound ν

/-- **Proved Bridge (`periodicTetherClosingBound_of_directionDepletion`):**
The cubic direction-depletion differential inequality hypothesis `PeriodicDirectionDepletionBound ν`
implies the uniform periodic vorticity ceiling `PeriodicTetherClosingBound ν` with explicit ceiling
`Y = max ‖ω₀‖_∞ (C_CZ / κ'')`. -/
public theorem periodicTetherClosingBound_of_directionDepletion (ν : ℝ)
    (hDepl : PeriodicDirectionDepletionBound ν) :
    PeriodicTetherClosingBound ν := by
  intro u₀ hu₀
  obtain ⟨C_CZ, κ'', hC_pos, hκ_pos, htraj⟩ := hDepl u₀ hu₀
  let Y := max (vorticity_sup_norm (vorticity u₀)) (C_CZ / κ'')
  have hY_nonneg : 0 ≤ Y :=
    le_trans (le_of_lt (div_pos hC_pos hκ_pos)) (le_max_right _ _)
  refine ⟨Y, hY_nonneg, ?_⟩
  intro T u p hsol t ht
  obtain ⟨hdiff, hode⟩ := htraj T u p hsol
  have hu0_eq : u 0 = u₀ := funext hsol.2.2.2.2.2.2.2.1
  have hceil := comparison_ode_ceiling
    (fun s => vorticity_sup_norm (vorticity (u s))) T C_CZ κ'' hC_pos hκ_pos hdiff hode t ht
  simpa [Y, hu0_eq] using hceil

/-- **Conditional Hypothesis 2 (`PeriodicBKMContinuation` — Classical PDE Input):**
If every local periodic smooth solution from `u₀` obeys a time-independent `L^∞` vorticity bound
`‖ω(t)‖_∞ ≤ Y`, then the local periodic solution extends globally to a jointly smooth periodic
solution `(u, p) ∈ C^∞([0, ∞) × ℝ³)` satisfying `IsPeriodicSmoothSolution ν u₀ 0 u p`
(Kato 1972 + Beale–Kato–Majda 1984 + parabolic regularity bootstrap on `𝕋³`). -/
@[expose] public def PeriodicBKMContinuation (ν : ℝ) : Prop :=
  0 < ν →
  ∀ u₀ : VelocityField,
    IsPeriodicSmoothInitialData u₀ →
    (∃ Y : ℝ, 0 ≤ Y ∧
      ∀ (T : ℝ) (u : TimeDependentVelocity) (p : TimeDependentPressure),
        IsPeriodicSmoothSolutionOn ν u₀ (fun _ _ => 0) T u p →
        ∀ t ∈ Set.Icc (0 : ℝ) T,
          vorticity_sup_norm (vorticity (u t)) ≤ Y) →
    ∃ (u : TimeDependentVelocity) (p : TimeDependentPressure),
      IsPeriodicSmoothSolution ν u₀ (fun _ _ => 0) u p

/-- **Conditional Reduction Theorem 1 (`clay_B_exact_of_periodic_tether_bound`):**
Conditional on `PeriodicTetherClosingBound ν` (OPEN) and `PeriodicBKMContinuation ν`, the exact
Fefferman Clay Statement (B) (`Clay_B_exact ν`) holds. -/
public theorem clay_B_exact_of_periodic_tether_bound (ν : ℝ)
    (hTether : PeriodicTetherClosingBound ν)
    (hBKM : PeriodicBKMContinuation ν) :
    Clay_B_exact ν := by
  intro hν u₀ hu₀
  exact hBKM hν u₀ hu₀ (hTether u₀ hu₀)

/-- **Conditional Reduction Theorem 2 (`clay_B_exact_of_torus_direction_depletion`):**
Conditional on `PeriodicDirectionDepletionBound ν` (OPEN) and `PeriodicBKMContinuation ν`, the exact
Fefferman Clay Statement (B) (`Clay_B_exact ν`) holds via the cubic comparison ODE ceiling
`Y = max ‖ω₀‖_∞ (C_CZ / κ'')`. -/
public theorem clay_B_exact_of_torus_direction_depletion (ν : ℝ)
    (hDepl : PeriodicDirectionDepletionBound ν)
    (hBKM : PeriodicBKMContinuation ν) :
    Clay_B_exact ν :=
  clay_B_exact_of_periodic_tether_bound ν
    (periodicTetherClosingBound_of_directionDepletion ν hDepl) hBKM

/-! ### Finite-horizon form (what Statement (B) needs)

Statement (B) asks for a smooth periodic solution on `[0, ∞)` with bounded energy. It does not
ask for a bound on `‖ω(t)‖_∞` that is uniform in `t`. The Beale–Kato–Majda continuation only
needs, for each horizon `T`, a bound `C(T)` on `[0, T]` that may depend on `T` and on `u₀`. -/

/-- **Conditional Hypothesis 1c (`PeriodicFiniteTimeVorticityBound` — OPEN):**
For every smooth, divergence-free, `ℤ³`-periodic initial datum `u₀` and every horizon `T ≥ 0`
there is `C(T) ≥ 0` (depending on `T`, `u₀`, `ν`) with `‖ω(t)‖_∞ ≤ C(T)` for `t ∈ [0, T]` along any
periodic smooth solution on `[0, T]`. -/
@[expose] public def PeriodicFiniteTimeVorticityBound (ν : ℝ) : Prop :=
  ∀ u₀ : VelocityField,
    IsPeriodicSmoothInitialData u₀ →
    ∀ T : ℝ, 0 ≤ T → ∃ C : ℝ, 0 ≤ C ∧
      ∀ (u : TimeDependentVelocity) (p : TimeDependentPressure),
        IsPeriodicSmoothSolutionOn ν u₀ (fun _ _ => 0) T u p →
        ∀ t ∈ Set.Icc (0 : ℝ) T,
          vorticity_sup_norm (vorticity (u t)) ≤ C

/-- **Conditional Hypothesis 2' (`PeriodicBKMContinuationFiniteTime` — Classical PDE Input):**
If every local periodic smooth solution from `u₀` obeys, on each horizon `[0, T]`, a bound
`‖ω(t)‖_∞ ≤ C(T)`, then the solution extends to a global periodic smooth solution
(Kato 1972 + Beale–Kato–Majda 1984 + parabolic bootstrap on `𝕋³`). This is the form in which
BKM is classically stated; it implies the uniform-input `PeriodicBKMContinuation`. -/
@[expose] public def PeriodicBKMContinuationFiniteTime (ν : ℝ) : Prop :=
  0 < ν →
  ∀ u₀ : VelocityField,
    IsPeriodicSmoothInitialData u₀ →
    (∀ T : ℝ, 0 ≤ T → ∃ C : ℝ, 0 ≤ C ∧
      ∀ (u : TimeDependentVelocity) (p : TimeDependentPressure),
        IsPeriodicSmoothSolutionOn ν u₀ (fun _ _ => 0) T u p →
        ∀ t ∈ Set.Icc (0 : ℝ) T,
          vorticity_sup_norm (vorticity (u t)) ≤ C) →
    ∃ (u : TimeDependentVelocity) (p : TimeDependentPressure),
      IsPeriodicSmoothSolution ν u₀ (fun _ _ => 0) u p

/-- **Proved:** the uniform ceiling implies the finite-horizon bound (`C(T) = Y`). -/
public theorem periodicFiniteTimeVorticityBound_of_uniform (ν : ℝ)
    (h : PeriodicTetherClosingBound ν) :
    PeriodicFiniteTimeVorticityBound ν := by
  intro u₀ hu₀ T _hT
  obtain ⟨Y, hY, hb⟩ := h u₀ hu₀
  exact ⟨Y, hY, fun u p hsol t ht => hb T u p hsol t ht⟩

/-- **Proved:** finite-horizon BKM continuation implies the uniform-input form. -/
public theorem periodicBKMContinuation_of_finiteTime (ν : ℝ)
    (h : PeriodicBKMContinuationFiniteTime ν) :
    PeriodicBKMContinuation ν := by
  intro hν u₀ hu₀ hunif
  obtain ⟨Y, hY, hb⟩ := hunif
  exact h hν u₀ hu₀ (fun T _hT => ⟨Y, hY, fun u p hsol t ht => hb T u p hsol t ht⟩)

/-- **Conditional Reduction Theorem 3 (`clay_B_exact_of_periodic_finite_time_bound`):**
Conditional on `PeriodicFiniteTimeVorticityBound ν` (OPEN) and
`PeriodicBKMContinuationFiniteTime ν` (classical), `Clay_B_exact ν` holds. -/
public theorem clay_B_exact_of_periodic_finite_time_bound (ν : ℝ)
    (hFin : PeriodicFiniteTimeVorticityBound ν)
    (hBKM : PeriodicBKMContinuationFiniteTime ν) :
    Clay_B_exact ν := by
  intro hν u₀ hu₀
  exact hBKM hν u₀ hu₀ (hFin u₀ hu₀)

end FeffermanClayNS
