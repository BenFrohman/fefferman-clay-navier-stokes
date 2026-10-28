/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/
module

public import FeffermanClayNS.HighSetDepletionAndBKM

/-!
# Main Theorem (reduction), following Mathlib 4 naming & style conventions
-/

@[expose] public section

namespace FeffermanClayNS

/-- **Single named open estimate (`HasDirectionCurvatureCoercivity` / `DirectionCurvatureBound`).**
High-set direction-curvature / cubic depletion bound `M' ≤ C_CZ M² − κ'' M³` along every local
periodic smooth Navier–Stokes solution. **OPEN conjecture** (not proved). -/
abbrev HasDirectionCurvatureCoercivity (ν : ℝ) : Prop := PeriodicDirectionDepletionBound ν

/-- Alias in the headline statement. -/
abbrev DirectionCurvatureBound (ν : ℝ) : Prop := HasDirectionCurvatureCoercivity ν

/-- Dot-notation projection: `h.periodicTetherClosingBound` extracts the uniform vorticity ceiling
`Y = max ‖ω₀‖_∞ (C_CZ / κ'')` from `HasDirectionCurvatureCoercivity ν`. -/
theorem HasDirectionCurvatureCoercivity.periodicTetherClosingBound {ν : ℝ}
    (h : HasDirectionCurvatureCoercivity ν) : PeriodicTetherClosingBound ν :=
  periodicTetherClosingBound_of_directionDepletion ν h

/-- Dot-notation reduction: `h.clay_B_exact hBKM` deduces `Clay_B_exact ν` from
`h : HasDirectionCurvatureCoercivity ν` and `hBKM : PeriodicBKMContinuation ν`. -/
theorem HasDirectionCurvatureCoercivity.clay_B_exact {ν : ℝ}
    (h : HasDirectionCurvatureCoercivity ν) (hBKM : PeriodicBKMContinuation ν) :
    Clay_B_exact ν :=
  clay_B_exact_of_torus_direction_depletion ν h hBKM

/-- **Main Theorem (`clay_B_exact_of_hasDirectionCurvatureCoercivity`, Mathlib `conclusion_of_hypothesis` style).** -/
theorem clay_B_exact_of_hasDirectionCurvatureCoercivity (ν : ℝ) (_hν : 0 < ν)
    (hBKM : PeriodicBKMContinuation ν) (hDCB : HasDirectionCurvatureCoercivity ν) :
    Clay_B_exact ν :=
  hDCB.clay_B_exact hBKM

/-- **Headline Main Theorem (`clay_reduces_to_direction_curvature_bound`).**
Unconditional Lean reduction theorem: for all `ν > 0`, given `PeriodicBKMContinuation ν`,
`DirectionCurvatureBound ν → Clay_B_exact ν`. Converse is NOT proved. -/
theorem clay_reduces_to_direction_curvature_bound :
    ∀ ν : ℝ, 0 < ν → PeriodicBKMContinuation ν →
      (DirectionCurvatureBound ν → Clay_B_exact ν) :=
  clay_B_exact_of_hasDirectionCurvatureCoercivity

end FeffermanClayNS

end

/-! ### Mathlib 4 `UpperCamelCase` / `conclusion_of_hypothesis` aliases for Stage 1–5 definitions -/

/-- Mathlib `UpperCamelCase` alias for `Z3Periodic`. -/
abbrev IsZ3Periodic (f : (Fin 3 → ℝ) → ℝ) : Prop := Z3Periodic f

/-- Mathlib `conclusion_of_hypothesis` alias for `bochner_weitzenbock_pointwise`. -/
alias inner_laplacian_eq_laplacian_half_norm_sq_sub_norm_grad_sq := bochner_weitzenbock_pointwise

/-- Mathlib `conclusion_of_hypothesis` alias for `polar_grad_pythagoras`. -/
alias norm_polar_grad_sq_eq := polar_grad_pythagoras

/-- Mathlib `conclusion_of_hypothesis` alias for `AttainedSpatialMaximum.vorticity_sup_norm_eq`. -/
theorem vorticity_sup_norm_eq_of_attainedSpatialMaximum
    {ω : ℝ × (Fin 3 → ℝ) → (Fin 3 → ℝ)} {t : ℝ} {x₀ : Fin 3 → ℝ}
    (h : AttainedSpatialMaximum ω t x₀) :
    vorticity_sup_norm ω t = Vec3.norm (ω (t, x₀)) :=
  h.vorticity_sup_norm_eq
