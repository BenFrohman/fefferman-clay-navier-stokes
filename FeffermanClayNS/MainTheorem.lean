/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/
module

public import FeffermanClayNS.HighSetDepletionAndBKM

/-!
# Main Theorem (reduction)

`clay_reduces_to_direction_curvature_bound`: for every `ν > 0`, the single named open estimate
`DirectionCurvatureBound ν`, together with the classical periodic Beale–Kato–Majda continuation
principle `PeriodicBKMContinuation ν` (Kato 1972, Beale–Kato–Majda 1984; a published theorem that
is **not** formalized here and is therefore an explicit hypothesis), implies Fefferman's exact
periodic Clay statement `Clay_B_exact ν`.

* This is a reduction, not a resolution: `DirectionCurvatureBound ν` is OPEN.
* The converse (`Clay_B_exact ν → DirectionCurvatureBound ν`) is NOT proved.
-/

@[expose] public section

namespace FeffermanClayNS

/-- **The single named open estimate (conjecture).** The high-set direction-curvature /
cubic depletion bound `M' ≤ C_CZ M² − κ'' M³` for `M(t) = ‖ω(t)‖_∞` along every local periodic
smooth Navier–Stokes solution. OPEN. -/
abbrev DirectionCurvatureBound (ν : ℝ) : Prop := PeriodicDirectionDepletionBound ν

/-- **Main Theorem (proved reduction).** -/
theorem clay_reduces_to_direction_curvature_bound :
    ∀ ν : ℝ, 0 < ν → PeriodicBKMContinuation ν →
      (DirectionCurvatureBound ν → Clay_B_exact ν) :=
  fun ν _ hBKM hDCB => clay_B_exact_of_torus_direction_depletion ν hDCB hBKM

end FeffermanClayNS

end
