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

2. **Cubic Comparison ODE Ceiling (`comparison_ode_ceiling`, one-sided `comparison_ode_ceiling_right`):**
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

/-- **One-sided cubic comparison ceiling (`comparison_ode_ceiling_right`):**
If `M` is continuous on `[0, T]` and at every `s ∈ [0, T)` has a right derivative `d` with
`d ≤ C_CZ * M(s)² - κ'' * M(s)³` (`C_CZ, κ'' > 0`), then `M t ≤ max (M 0) (C_CZ / κ'')` on `[0, T]`.
Only values of `M` on `[0, T]` are used. -/
public theorem comparison_ode_ceiling_right
    (M : ℝ → ℝ) (T C_CZ κ'' : ℝ)
    (hC_pos : 0 < C_CZ) (hκ_pos : 0 < κ'')
    (hM_cont : ContinuousOn M (Set.Icc (0 : ℝ) T))
    (hODE : ∀ s ∈ Set.Ico (0 : ℝ) T, ∃ d : ℝ,
      HasDerivWithinAt M d (Set.Ici s) s ∧ d ≤ C_CZ * (M s) ^ 2 - κ'' * (M s) ^ 3) :
    ∀ t ∈ Set.Icc (0 : ℝ) T, M t ≤ max (M 0) (C_CZ / κ'') := by
  intro t ht
  choose! d hd hdle using hODE
  set Y := max (M 0) (C_CZ / κ'')
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hbarrier : C_CZ / κ'' < Y + ε :=
    lt_of_le_of_lt (le_max_right (M 0) (C_CZ / κ'')) (lt_add_of_pos_right _ hε)
  have hM0 : M 0 ≤ Y + ε :=
    (le_max_left (M 0) (C_CZ / κ'')).trans (le_add_of_nonneg_right hε.le)
  have hMC : ContinuousOn M (Set.Icc (0 : ℝ) t) :=
    hM_cont.mono (Set.Icc_subset_Icc_right ht.2)
  have hMW : ∀ x ∈ Set.Ico (0 : ℝ) t, HasDerivWithinAt M (d x) (Set.Ici x) x := fun x hx =>
    hd x ⟨hx.1, lt_of_lt_of_le hx.2 ht.2⟩
  have hB : ∀ x, HasDerivAt (fun _ : ℝ => Y + ε) (0 : ℝ) x := fun x =>
    hasDerivAt_const x (Y + ε)
  have hcontact : ∀ x ∈ Set.Ico (0 : ℝ) t, M x = Y + ε → d x < 0 := by
    intro x hx hxeq
    have hneg : C_CZ * (Y + ε) ^ 2 - κ'' * (Y + ε) ^ 3 < 0 :=
      cubic_comparison_field_neg_of_gt hC_pos hκ_pos hbarrier
    have hdot := hdle x ⟨hx.1, lt_of_lt_of_le hx.2 ht.2⟩
    rw [hxeq] at hdot
    linarith
  have hle :=
    image_le_of_deriv_right_lt_deriv_boundary (f := M) (f' := d)
      (a := 0) (b := t) (B := fun _ => Y + ε) (B' := fun _ => (0 : ℝ))
      hMC hMW hM0 hB hcontact
  exact hle ⟨ht.1, le_rfl⟩

/-! ## Conditional Periodic Hypotheses & Conditional Reductions to `Clay_B_exact`

**Honesty & Scope Notice:**
Both `PeriodicDirectionDepletionBound ν` and `PeriodicTetherClosingBound ν` below are **OPEN**
analytic hypotheses on the periodic 3-torus `𝕋³ = ℝ³ / ℤ³`. They are defined as `Prop`s and
passed explicitly as hypotheses to the conditional reduction theorems
`clay_B_exact_of_periodic_tether_bound` and `clay_B_exact_of_torus_direction_depletion`. -/

/-- **Conditional Hypothesis 1a (`PeriodicDirectionDepletionBound` — OPEN, corrected in v1.5.0):**
For every smooth, divergence-free, `ℤ³`-periodic initial datum `u₀`, there exist positive
constants `C_CZ, κ'' > 0` such that along any local-in-time periodic smooth solution `(u, p)` on
`[0, T] × (ℝ³ / ℤ³)`, the spatial supremum of vorticity `M(t) = ‖ω(t)‖_∞` is continuous on
`[0, T]` and, at every `s ∈ [0, T)`, has a right derivative `d` (`HasDerivWithinAt … (Set.Ici s) s`)
with `d ≤ C_CZ * M(s)² - κ'' * M(s)³`.

The hypothesis only reads `M` on `[0, T]`, the interval on which `IsPeriodicSmoothSolutionOn`
constrains `u`. The v1.0–v1.4 form (kept below as `PeriodicDirectionDepletionBoundOriginal`) asked
for a two-sided derivative at every `t ∈ [0, T]`, including the endpoints, and is unsatisfiable
(`old_periodicDirectionDepletionBound_unsatisfiable`). -/
@[expose] public def PeriodicDirectionDepletionBound (ν : ℝ) : Prop :=
  ∀ u₀ : VelocityField,
    IsPeriodicSmoothInitialData u₀ →
    ∃ C_CZ κ'' : ℝ, 0 < C_CZ ∧ 0 < κ'' ∧
      ∀ (T : ℝ) (u : TimeDependentVelocity) (p : TimeDependentPressure),
        IsPeriodicSmoothSolutionOn ν u₀ (fun _ _ => 0) T u p →
        ContinuousOn (fun s => vorticity_sup_norm (vorticity (u s))) (Set.Icc (0 : ℝ) T) ∧
        (∀ s ∈ Set.Ico (0 : ℝ) T, ∃ d : ℝ,
          HasDerivWithinAt (fun τ => vorticity_sup_norm (vorticity (u τ))) d (Set.Ici s) s ∧
            d ≤ C_CZ * (vorticity_sup_norm (vorticity (u s))) ^ 2 -
              κ'' * (vorticity_sup_norm (vorticity (u s))) ^ 3)

/-- **Scaffolding (unsatisfiable):** the v1.0–v1.4 form of `PeriodicDirectionDepletionBound`,
with a two-sided derivative at every `t ∈ [0, T]`. A solution on `[0, T]` is unconstrained for
`t < 0`, so the derivative at `t = 0` can always be destroyed; see
`old_periodicDirectionDepletionBound_unsatisfiable`. Every implication from this hypothesis was
vacuously true. -/
@[expose] public def PeriodicDirectionDepletionBoundOriginal (ν : ℝ) : Prop :=
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
  obtain ⟨hcont, hode⟩ := htraj T u p hsol
  have hu0_eq : u 0 = u₀ := funext hsol.2.2.2.2.2.2.2
  have hceil := comparison_ode_ceiling_right
    (fun s => vorticity_sup_norm (vorticity (u s))) T C_CZ κ'' hC_pos hκ_pos hcont hode t ht
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

/-- **Proved (scaffolding):** finite-horizon continuation implies the uniform-input form. Both
forms quantify only over solutions that already exist on `[0, T]`, so they place the whole
continuation content in the hypothesis; see `periodicFiniteTimeBound_vacuous`. -/
public theorem periodicBKMContinuation_of_finiteTime_scaffold (ν : ℝ)
    (h : PeriodicBKMContinuationFiniteTime ν) :
    PeriodicBKMContinuation ν := by
  intro hν u₀ hu₀ hunif
  obtain ⟨Y, hY, hb⟩ := hunif
  exact h hν u₀ hu₀ (fun T _hT => ⟨Y, hY, fun u p hsol t ht => hb T u p hsol t ht⟩)

/-- **Proved (scaffolding):** `Clay_B_exact` from `PeriodicFiniteTimeVorticityBound` and
`PeriodicBKMContinuationFiniteTime`. The second hypothesis carries all of Statement (B). -/
public theorem clay_B_exact_of_periodic_finite_time_bound_scaffold (ν : ℝ)
    (hFin : PeriodicFiniteTimeVorticityBound ν)
    (hBKM : PeriodicBKMContinuationFiniteTime ν) :
    Clay_B_exact ν := by
  intro hν u₀ hu₀
  exact hBKM hν u₀ hu₀ (hFin u₀ hu₀)

/-- **Proved:** on a horizon where no periodic smooth solution exists, the finite-time vorticity
bound holds with `C = 0`. The bound in `PeriodicFiniteTimeVorticityBound` therefore says nothing
past the existence time. -/
public theorem periodicFiniteTimeBound_vacuous (ν : ℝ) (u₀ : VelocityField) (T : ℝ)
    (hnone : ∀ (u : TimeDependentVelocity) (p : TimeDependentPressure),
      ¬ IsPeriodicSmoothSolutionOn ν u₀ (fun _ _ => 0) T u p) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (u : TimeDependentVelocity) (p : TimeDependentPressure),
        IsPeriodicSmoothSolutionOn ν u₀ (fun _ _ => 0) T u p →
        ∀ t ∈ Set.Icc (0 : ℝ) T, vorticity_sup_norm (vorticity (u t)) ≤ C :=
  ⟨0, le_refl 0, fun u p hsol => absurd hsol (hnone u p)⟩

/-! ### Periodic Beale–Kato–Majda step

The maximal existence time `periodicTstar ν u₀` is the supremum, in `EReal`, of the horizons `T`
on which a periodic smooth solution from `u₀` exists. Global existence is derived from
`periodicTstar ν u₀ = ⊤` through the BKM criterion and BKM integrability.

Correction. Earlier versions used `IsPeriodicSmoothSolutionOnOriginal` (with an L²(ℝ³) clause),
and `IsPeriodicMaximalSolution` quantified over all `T < periodicTstar`, including `T ≤ 0`. With
those definitions `PeriodicLocalExistence ν` and `PeriodicMaximalSolution ν` are false for every
`ν > 0` (proved below as `not_periodicLocalExistenceOriginal` and
`not_periodicMaximalSolutionOriginal`). The definitions now use the corrected
`IsPeriodicSmoothSolutionOn` and require maximality only for `0 < T`. The old ones are kept below
as scaffolding with the suffix `Original`. -/

/-- Horizons on which a periodic smooth solution from `u₀` exists. -/
@[expose] public def periodicExistenceTimes (ν : ℝ) (u₀ : VelocityField) : Set EReal :=
  {s | ∃ T : ℝ, s = (T : EReal) ∧ ∃ (u : TimeDependentVelocity) (p : TimeDependentPressure),
    IsPeriodicSmoothSolutionOn ν u₀ (fun _ _ => 0) T u p}

/-- Maximal periodic existence time. -/
@[expose] public noncomputable def periodicTstar (ν : ℝ) (u₀ : VelocityField) : EReal :=
  sSup (periodicExistenceTimes ν u₀)

/-- A pair `(u, p)` that is a periodic smooth solution on every `[0, T]` with
`0 < T < periodicTstar`. -/
@[expose] public def IsPeriodicMaximalSolution (ν : ℝ) (u₀ : VelocityField)
    (u : TimeDependentVelocity) (p : TimeDependentPressure) : Prop :=
  ∀ T : ℝ, 0 < T → (T : EReal) < periodicTstar ν u₀ →
    IsPeriodicSmoothSolutionOn ν u₀ (fun _ _ => 0) T u p

/-- **Classical (Kato 1972), not formalized:** positive local existence time. -/
@[expose] public def PeriodicLocalExistence (ν : ℝ) : Prop :=
  0 < ν → ∀ u₀ : VelocityField, IsPeriodicSmoothInitialData u₀ → (0 : EReal) < periodicTstar ν u₀

/-- **Classical (uniqueness and gluing):** a single maximal solution. Proved from velocity
uniqueness in the companion repository `periodic-ns-classical-continuation`. -/
@[expose] public def PeriodicMaximalSolution (ν : ℝ) : Prop :=
  0 < ν → ∀ u₀ : VelocityField, IsPeriodicSmoothInitialData u₀ →
    ∃ (u : TimeDependentVelocity) (p : TimeDependentPressure), IsPeriodicMaximalSolution ν u₀ u p

/-- A maximal solution with `periodicTstar = ⊤` is a periodic smooth solution in the sense of
Statement (B). Proved below: `periodicGlobalOfTstarTop`. -/
@[expose] public def PeriodicGlobalOfTstarTop (ν : ℝ) : Prop :=
  0 < ν → ∀ u₀ : VelocityField, IsPeriodicSmoothInitialData u₀ →
    ∀ (u : TimeDependentVelocity) (p : TimeDependentPressure),
      IsPeriodicMaximalSolution ν u₀ u p → periodicTstar ν u₀ = ⊤ →
      ∃ (u' : TimeDependentVelocity) (p' : TimeDependentPressure),
        IsPeriodicSmoothSolution ν u₀ (fun _ _ => 0) u' p'

/-- **Classical (Beale–Kato–Majda 1984), not formalized:** if `periodicTstar = T` is finite,
`‖ω(t)‖_∞` is not integrable on `[0, T]` along the maximal solution. -/
@[expose] public def PeriodicBKMCriterion (ν : ℝ) : Prop :=
  0 < ν → ∀ u₀ : VelocityField, IsPeriodicSmoothInitialData u₀ →
    ∀ (u : TimeDependentVelocity) (p : TimeDependentPressure),
      IsPeriodicMaximalSolution ν u₀ u p →
      ∀ T : ℝ, periodicTstar ν u₀ = (T : EReal) →
        ¬ IntegrableOn (fun t => vorticity_sup_norm (vorticity (u t))) (Set.Icc 0 T)

/-- **OPEN:** `‖ω(t)‖_∞` is integrable on every `[0, T]` along the maximal solution. -/
@[expose] public def PeriodicBKMIntegrability (ν : ℝ) : Prop :=
  0 < ν → ∀ u₀ : VelocityField, IsPeriodicSmoothInitialData u₀ →
    ∀ (u : TimeDependentVelocity) (p : TimeDependentPressure),
      IsPeriodicMaximalSolution ν u₀ u p →
      ∀ T : ℝ, IntegrableOn (fun t => vorticity_sup_norm (vorticity (u t))) (Set.Icc 0 T)

/-- **Proved:** `periodicTstar ν u₀ = ⊤` along a maximal solution, from local existence, the BKM
criterion and BKM integrability. -/
public theorem periodicTstar_eq_top_of_bkm (ν : ℝ) (hν : 0 < ν)
    (hloc : PeriodicLocalExistence ν) (hcrit : PeriodicBKMCriterion ν)
    (hint : PeriodicBKMIntegrability ν) (u₀ : VelocityField) (hu₀ : IsPeriodicSmoothInitialData u₀)
    (u : TimeDependentVelocity) (p : TimeDependentPressure)
    (hmax : IsPeriodicMaximalSolution ν u₀ u p) :
    periodicTstar ν u₀ = ⊤ :=
  ereal_eq_top_of_bkm _ _ (hloc hν u₀ hu₀) (hcrit hν u₀ hu₀ u p hmax)
    (hint hν u₀ hu₀ u p hmax)

lemma Icc_mem_nhdsWithin_Ici_prod (t : ℝ) (x : T3) :
    Set.Icc (0 : ℝ) (t + 1) ×ˢ (Set.univ : Set T3) ∈
      𝓝[Set.Ici (0 : ℝ) ×ˢ Set.univ] (t, x) := by
  refine mem_nhdsWithin.2 ⟨Set.Iio (t + 1) ×ˢ Set.univ, isOpen_Iio.prod isOpen_univ,
    ⟨by simp, trivial⟩, ?_⟩
  rintro ⟨a, b⟩ ⟨⟨ha, -⟩, ha', -⟩
  exact ⟨⟨ha', (show a < t + 1 from ha).le⟩, trivial⟩

lemma hasDerivWithinAt_slice_Icc {T : ℝ} {u : TimeDependentVelocity}
    (hu : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun q : ℝ × T3 => u q.1 q.2)
      (Set.Icc (0 : ℝ) T ×ˢ Set.univ))
    (x : T3) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    HasDerivWithinAt (fun s => u s x) (derivWithin (fun s => u s x) (Set.Icc (0 : ℝ) T) t)
      (Set.Icc (0 : ℝ) T) t := by
  have hc : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun s : ℝ => u s x) (Set.Icc (0 : ℝ) T) :=
    hu.comp ((contDiff_id.prodMk contDiff_const).contDiffOn) (fun _ hs => ⟨hs, trivial⟩)
  exact ((hc.differentiableOn (by simp)) t ht).hasDerivWithinAt

/-- **Proved:** a pair that solves on every positive horizon solves Statement (B). -/
public theorem isPeriodicSmoothSolution_of_forall_horizon {ν : ℝ} {u₀ : VelocityField}
    {u : TimeDependentVelocity} {p : TimeDependentPressure}
    (h : ∀ T : ℝ, 0 < T → IsPeriodicSmoothSolutionOn ν u₀ (fun _ _ => 0) T u p) :
    IsPeriodicSmoothSolution ν u₀ (fun _ _ => 0) u p := by
  have hS : ∀ t : ℝ, 0 ≤ t → IsPeriodicSmoothSolutionOn ν u₀ (fun _ _ => 0) (t + 1) u p :=
    fun t ht => h (t + 1) (by linarith)
  have hmem : ∀ t : ℝ, 0 ≤ t → t ∈ Set.Icc (0 : ℝ) (t + 1) := fun t ht => ⟨ht, by linarith⟩
  refine ⟨fun t ht => (hS t ht).2.1 t (hmem t ht), fun t ht => (hS t ht).2.2.1 t (hmem t ht),
    ?_, ?_, ?_, fun t ht => (hS t ht).2.2.2.2.2.2.1 t (hmem t ht), (h 1 one_pos).2.2.2.2.2.2.2⟩
  · rintro ⟨t, x⟩ ⟨ht, -⟩
    exact ((hS t ht).2.2.2.1 (t, x) ⟨hmem t ht, trivial⟩).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsWithin_Ici_prod t x)
  · rintro ⟨t, x⟩ ⟨ht, -⟩
    exact ((hS t ht).2.2.2.2.1 (t, x) ⟨hmem t ht, trivial⟩).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsWithin_Ici_prod t x)
  · intro t ht x
    have hd := hasDerivWithinAt_slice_Icc (hS t ht).2.2.2.1 x (hmem t ht)
    have hnhds : Set.Icc (0 : ℝ) (t + 1) ∈ 𝓝[Set.Ici (0 : ℝ)] t := by
      refine mem_nhdsWithin.2 ⟨Set.Iio (t + 1), isOpen_Iio, by simp, ?_⟩
      rintro a ⟨ha, ha'⟩
      exact ⟨ha', (show a < t + 1 from ha).le⟩
    have hd' := hd.mono_of_mem_nhdsWithin hnhds
    rw [hd'.derivWithin ((uniqueDiffOn_Ici 0) t ht)]
    exact (hS t ht).2.2.2.2.2.1 t (hmem t ht) x

/-- **Proved:** `PeriodicGlobalOfTstarTop ν` holds for every `ν`. -/
public theorem periodicGlobalOfTstarTop (ν : ℝ) : PeriodicGlobalOfTstarTop ν := by
  intro _ u₀ _ u p hmax htop
  exact ⟨u, p, isPeriodicSmoothSolution_of_forall_horizon
    (fun T hT => hmax T hT (by rw [htop]; exact EReal.coe_lt_top T))⟩

/-- **Conditional Reduction Theorem 3 (`clay_B_exact_of_periodic_bkm`):**
`Clay_B_exact ν` from the classical inputs `PeriodicLocalExistence`, `PeriodicMaximalSolution`,
`PeriodicBKMCriterion` and the OPEN `PeriodicBKMIntegrability`. The global step is proved
(`periodicGlobalOfTstarTop`). -/
public theorem clay_B_exact_of_periodic_bkm (ν : ℝ)
    (hloc : PeriodicLocalExistence ν) (hmax : PeriodicMaximalSolution ν)
    (hcrit : PeriodicBKMCriterion ν) (hint : PeriodicBKMIntegrability ν) :
    Clay_B_exact ν := by
  intro hν u₀ hu₀
  obtain ⟨u, p, hm⟩ := hmax hν u₀ hu₀
  exact periodicGlobalOfTstarTop ν hν u₀ hu₀ u p hm
    (periodicTstar_eq_top_of_bkm ν hν hloc hcrit hint u₀ hu₀ u p hm)

/-! ### Scaffolding: the earlier (unsatisfiable) definitions and their refutation -/

/-- Earlier existence horizons, using `IsPeriodicSmoothSolutionOnOriginal`. -/
@[expose] public def periodicExistenceTimesOriginal (ν : ℝ) (u₀ : VelocityField) : Set EReal :=
  {s | ∃ T : ℝ, s = (T : EReal) ∧ ∃ (u : TimeDependentVelocity) (p : TimeDependentPressure),
    IsPeriodicSmoothSolutionOnOriginal ν u₀ (fun _ _ => 0) T u p}

/-- Earlier maximal existence time. -/
@[expose] public noncomputable def periodicTstarOriginal (ν : ℝ) (u₀ : VelocityField) : EReal :=
  sSup (periodicExistenceTimesOriginal ν u₀)

/-- Earlier maximality predicate (quantifies also over `T ≤ 0`). -/
@[expose] public def IsPeriodicMaximalSolutionOriginal (ν : ℝ) (u₀ : VelocityField)
    (u : TimeDependentVelocity) (p : TimeDependentPressure) : Prop :=
  ∀ T : ℝ, (T : EReal) < periodicTstarOriginal ν u₀ →
    IsPeriodicSmoothSolutionOnOriginal ν u₀ (fun _ _ => 0) T u p

/-- Earlier local existence statement. -/
@[expose] public def PeriodicLocalExistenceOriginal (ν : ℝ) : Prop :=
  0 < ν → ∀ u₀ : VelocityField, IsPeriodicSmoothInitialData u₀ →
    (0 : EReal) < periodicTstarOriginal ν u₀

/-- Earlier maximal-solution statement. -/
@[expose] public def PeriodicMaximalSolutionOriginal (ν : ℝ) : Prop :=
  0 < ν → ∀ u₀ : VelocityField, IsPeriodicSmoothInitialData u₀ →
    ∃ (u : TimeDependentVelocity) (p : TimeDependentPressure),
      IsPeriodicMaximalSolutionOriginal ν u₀ u p

/-- The constant velocity field `e₀`. -/
public noncomputable def constE0 : VelocityField := fun _ => EuclideanSpace.single 0 1

public theorem constE0_initialData : IsPeriodicSmoothInitialData constE0 := by
  refine ⟨contDiff_const, ?_, ?_⟩
  · intro x; simp [div, constE0]
  · intro x k; rfl

/-- **Proved:** a field equal to `e₀` at `t = 0` is never an `IsPhysicalNSSolution`. -/
public theorem not_isPhysicalNSSolution_of_constE0 (u : TimeDependentVelocity)
    (h0 : u 0 = constE0) : ¬ IsPhysicalNSSolution u := by
  rintro ⟨-, -, hint, -, -⟩
  have := hint 0 le_rfl
  rw [h0] at this
  simp [constE0, integrable_const_iff] at this
  have h := MeasureTheory.measure_univ_of_isAddLeftInvariant (MeasureTheory.volume : Measure T3)
  exact absurd h (measure_ne_top _ _)

public theorem periodicExistenceTimesOriginal_constE0 (ν : ℝ) :
    periodicExistenceTimesOriginal ν constE0 = ∅ := by
  ext s
  simp only [periodicExistenceTimesOriginal, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  rintro ⟨T, -, u, p, hsol, hphys⟩
  exact not_isPhysicalNSSolution_of_constE0 u (funext hsol.2.2.2.2.2.2.2) hphys

/-- **Proved:** the earlier `PeriodicLocalExistenceOriginal ν` is false for every `ν > 0`. -/
public theorem not_periodicLocalExistenceOriginal (ν : ℝ) (hν : 0 < ν) :
    ¬ PeriodicLocalExistenceOriginal ν := by
  intro h
  have := h hν constE0 constE0_initialData
  simp [periodicTstarOriginal, periodicExistenceTimesOriginal_constE0] at this

/-- The zero pair solves on `[0, 1]` from zero data (corrected predicate). -/
public theorem zero_isPeriodicSmoothSolutionOn (ν : ℝ) :
    IsPeriodicSmoothSolutionOn ν 0 (fun _ _ => 0) 1 (fun _ => 0) (fun _ => 0) := by
  refine ⟨one_pos, fun _ _ _ _ => rfl, fun _ _ _ _ => rfl, contDiffOn_const, contDiffOn_const,
    ?_, ?_, fun _ => rfl⟩
  · intro t _ x
    simp [convective, laplacian, pressureGradient, gradient]
  · intro t _ x
    simp [div]

public theorem zero_isPeriodicSmoothInitialData : IsPeriodicSmoothInitialData 0 := by
  refine ⟨contDiff_const, ?_, fun _ _ => rfl⟩
  intro x; simp [div]

/-- **Proved:** the earlier `PeriodicMaximalSolutionOriginal ν` is false for every `ν > 0`: it
asks for a solution on the horizon `T = -1`. -/
public theorem not_periodicMaximalSolutionOriginal (ν : ℝ) (hν : 0 < ν) :
    ¬ PeriodicMaximalSolutionOriginal ν := by
  intro h
  obtain ⟨u, p, hmax⟩ := h hν 0 zero_isPeriodicSmoothInitialData
  have hmem : ((1 : ℝ) : EReal) ∈ periodicExistenceTimesOriginal ν 0 :=
    ⟨1, rfl, _, _, zero_isPeriodicSmoothSolutionOn ν, isPhysicalNSSolution_zero⟩
  have hlt : ((-1 : ℝ) : EReal) < periodicTstarOriginal ν 0 :=
    lt_of_lt_of_le (EReal.coe_lt_coe_iff.2 (by norm_num)) (le_sSup hmem)
  exact absurd (hmax (-1) hlt).1.1 (by norm_num)


/-! ### v1.5.0 erratum: the two-sided-derivative hypothesis was unsatisfiable

`PeriodicDirectionDepletionBoundOriginal` (the v1.0–v1.4 `PeriodicDirectionDepletionBound`) asked
for `DifferentiableAt` of `M(t) = ‖ω(t)‖_∞` at `t = 0`. `IsPeriodicSmoothSolutionOn` says nothing
about `u t` for `t < 0`. The path `jumpPath` is zero on `[0, ∞)` (so it solves from zero data on
`[0, 1]`) and equals a linear shear with nonzero constant vorticity for `t < 0`, so `M` jumps at
`0`. Hence the old hypothesis fails for every `ν`, and the old main implication was vacuous. -/

/-- The linear shear `x ↦ x₀ e₁` as a continuous linear map. -/
public noncomputable def shearCLM : T3 →L[ℝ] T3 :=
  (EuclideanSpace.proj (0 : Fin 3)).smulRight (EuclideanSpace.single (1 : Fin 3) (1 : ℝ))

/-- The linear shear `x ↦ x₀ e₁` as a velocity field. -/
public noncomputable def shearField : VelocityField := fun y => shearCLM y

/-- Directional coordinates of a continuous linear field do not depend on the base point. -/
public theorem directionalCoord_clm (L : T3 →L[ℝ] T3) (comp dir : Fin 3) (x : T3) :
    directionalCoord (fun y => L y) comp dir x = L (EuclideanSpace.single dir 1) comp := by
  unfold directionalCoord
  have hfun : (fun y => L y comp) = ⇑((EuclideanSpace.proj comp).comp L) := by
    funext y
    simp
  rw [hfun, ContinuousLinearMap.fderiv]
  simp

public theorem curl_shearField (x : T3) : curl shearField x = curl shearField 0 := by
  simp only [curl, shearField, directionalCoord_clm]

public theorem curl_shearField_ne_zero : curl shearField 0 ≠ 0 := by
  intro h
  have h2 := congrArg (fun v : EuclideanSpace ℝ (Fin 3) => v 2) h
  simp [curl, shearField, directionalCoord_clm, shearCLM] at h2

public theorem vorticity_sup_norm_shearField_pos :
    0 < vorticity_sup_norm (vorticity shearField) := by
  have h : (fun x : T3 => ‖vorticity shearField x‖) = fun _ => ‖curl shearField 0‖ := by
    funext x
    simp only [vorticity]
    rw [curl_shearField x]
  unfold vorticity_sup_norm
  rw [h, ciSup_const]
  exact norm_pos_iff.2 curl_shearField_ne_zero

/-- Zero on `[0, ∞)`, the shear `shearField` for `t < 0`. -/
public noncomputable def jumpPath : TimeDependentVelocity :=
  fun s => if s < 0 then shearField else 0

public theorem jumpPath_of_nonneg {s : ℝ} (hs : 0 ≤ s) : jumpPath s = 0 := by
  simp [jumpPath, not_lt.2 hs]

/-- `jumpPath` solves on `[0, 1]` from zero data: it agrees with the zero solution there. -/
public theorem jumpPath_isPeriodicSmoothSolutionOn (ν : ℝ) :
    IsPeriodicSmoothSolutionOn ν 0 (fun _ _ => 0) 1 jumpPath (fun _ => 0) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, _h8⟩ := zero_isPeriodicSmoothSolutionOn ν
  refine ⟨h1, fun t ht => ?_, h3, ?_, h5, fun t ht x => ?_, fun t ht x => ?_, fun x => ?_⟩
  · rw [jumpPath_of_nonneg ht.1]
    exact h2 t ht
  · exact h4.congr fun q hq => by simp [jumpPath_of_nonneg hq.1.1]
  · have hEq : Set.EqOn (fun s => jumpPath s x) (fun s => (fun _ => (0 : VelocityField)) s x)
        (Set.Icc (0 : ℝ) 1) := fun s hs => by simp [jumpPath_of_nonneg hs.1]
    rw [derivWithin_congr hEq (hEq ht), jumpPath_of_nonneg ht.1]
    exact h6 t ht x
  · rw [jumpPath_of_nonneg ht.1]
    exact h7 t ht x
  · rw [jumpPath_of_nonneg le_rfl]

public theorem jumpPath_sup_norm :
    (fun s => vorticity_sup_norm (vorticity (jumpPath s))) =
      fun s => if s < 0 then vorticity_sup_norm (vorticity shearField) else 0 := by
  funext s
  by_cases hs : s < 0
  · simp [jumpPath, hs]
  · rw [if_neg hs, jumpPath_of_nonneg (not_lt.1 hs)]
    exact vorticity_sup_norm_zero_field

/-- A real function equal to `m ≠ 0` on `(-∞, 0)` and to `0` on `[0, ∞)` is not differentiable
at `0`. -/
public theorem not_differentiableAt_jump (m : ℝ) (hm : m ≠ 0) :
    ¬ DifferentiableAt ℝ (fun s : ℝ => if s < 0 then m else 0) 0 := by
  intro hd
  have hc := hd.continuousAt.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Iio (0 : ℝ)))
  have heq : (fun _ : ℝ => m) =ᶠ[𝓝[<] (0 : ℝ)] fun s : ℝ => if s < 0 then m else 0 :=
    eventually_nhdsWithin_of_forall fun s hs => (if_pos hs).symm
  have h2 : Tendsto (fun s : ℝ => if s < 0 then m else 0) (𝓝[<] (0 : ℝ)) (𝓝 m) :=
    tendsto_const_nhds.congr' heq
  have h3 := tendsto_nhds_unique hc h2
  simp only [lt_irrefl, if_false] at h3
  exact hm h3.symm

/-- **Proved (v1.5.0 erratum):** the v1.0–v1.4 hypothesis `PeriodicDirectionDepletionBoundOriginal ν`
is false for every `ν`. Every theorem that assumed it was vacuously true. -/
public theorem old_periodicDirectionDepletionBound_unsatisfiable (ν : ℝ) :
    ¬ PeriodicDirectionDepletionBoundOriginal ν := by
  intro h
  obtain ⟨_C, _κ, -, -, htraj⟩ := h 0 zero_isPeriodicSmoothInitialData
  obtain ⟨hdiff, -⟩ := htraj 1 jumpPath (fun _ => 0) (jumpPath_isPeriodicSmoothSolutionOn ν)
  have h0 := hdiff 0 ⟨le_rfl, zero_le_one⟩
  rw [jumpPath_sup_norm] at h0
  exact not_differentiableAt_jump _ (ne_of_gt vorticity_sup_norm_shearField_pos) h0

/-- **Proved (regression):** the trajectory clause of the corrected
`PeriodicDirectionDepletionBound` holds for `jumpPath` on every `[0, T]`, for any constants.
The corrected hypothesis is not refuted by values off `[0, T]`. -/
public theorem jumpPath_oneSided_depletion_clause (T C_CZ κ'' : ℝ) :
    ContinuousOn (fun s => vorticity_sup_norm (vorticity (jumpPath s))) (Set.Icc (0 : ℝ) T) ∧
    (∀ s ∈ Set.Ico (0 : ℝ) T, ∃ d : ℝ,
      HasDerivWithinAt (fun τ => vorticity_sup_norm (vorticity (jumpPath τ))) d (Set.Ici s) s ∧
        d ≤ C_CZ * (vorticity_sup_norm (vorticity (jumpPath s))) ^ 2 -
          κ'' * (vorticity_sup_norm (vorticity (jumpPath s))) ^ 3) := by
  have hz : ∀ τ : ℝ, 0 ≤ τ → vorticity_sup_norm (vorticity (jumpPath τ)) = 0 := fun τ hτ => by
    rw [jumpPath_of_nonneg hτ]
    exact vorticity_sup_norm_zero_field
  refine ⟨?_, fun s hs => ⟨0, ?_, ?_⟩⟩
  · exact continuousOn_const.congr fun τ hτ => hz τ hτ.1
  · exact (hasDerivWithinAt_const s (Set.Ici s) (0 : ℝ)).congr
      (fun τ hτ => hz τ (le_trans hs.1 hτ)) (hz s hs.1)
  · rw [hz s hs.1]
    simp

end FeffermanClayNS
