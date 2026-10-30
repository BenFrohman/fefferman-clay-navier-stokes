/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

-- In-Kernel Metaprogramming Axiom Audit (`Lean.collectAxioms` over `ConstantInfo.thmInfo`).
-- Run: `lake env lean AxiomAudit.lean`
-- Fails with non-zero exit if any theorem in the `FeffermanClayNS` module tree depends on
-- axioms outside {propext, Classical.choice, Quot.sound} (such as sorryAx or Lean.trustCompiler).

import Lean
import FeffermanClayNS

open Lean Elab Command

#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut stats : Std.HashMap Name (Nat × Nat) := {}
  let mut bad : Array String := #[]
  for (n, ci) in env.constants.toList do
    if n.isInternal then continue
    let some idx := env.getModuleIdxFor? n | continue
    let mod := env.header.moduleNames[idx.toNat]!
    unless (`FeffermanClayNS).isPrefixOf mod do continue
    unless ci matches .thmInfo _ do continue
    let axs ← liftCoreM <| Lean.collectAxioms n
    let nonstd := axs.filter (fun a => a ∉ [``propext, ``Classical.choice, ``Quot.sound])
    let (c, b) := stats.getD mod (0, 0)
    stats := stats.insert mod (c + 1, if nonstd.isEmpty then b else b + 1)
    unless nonstd.isEmpty do bad := bad.push s!"{n} : {nonstd}"
  for (m, (c, b)) in stats.toList do
    IO.println s!"{m}: theorems={c} nonstandard={b}"
  for s in bad do
    IO.println s
  let total := stats.fold (fun acc _ (c, _) => acc + c) 0
  IO.println s!"TOTAL theorems={total} nonstandard={bad.size}"
  unless bad.isEmpty do
    throwError "axiom audit FAILED: {bad.size} theorem(s) use non-standard axioms"

-- Explicit #print axioms checks on all primary exported theorems:
#print axioms FeffermanClayNS.isZ3Periodic_iff_unit_shifts
#print axioms FeffermanClayNS.clay_B_exact_of_with_energy
#print axioms FeffermanClayNS.library_huniq_unsatisfiable_at_zero
#print axioms FeffermanClayNS.repaired_huniq_at_zero
#print axioms FeffermanClayNS.z3_periodic_linear_eq_zero
#print axioms FeffermanClayNS.burgersLinearStrain_not_z3_periodic
#print axioms FeffermanClayNS.cross3_self
#print axioms FeffermanClayNS.det3_self_right
#print axioms FeffermanClayNS.biot_savart_det_aligned_eq_zero
#print axioms FeffermanClayNS.aligned_vorticity_stretching_integrand_zero
#print axioms FeffermanClayNS.biot_savart_det_difference_identity
#print axioms FeffermanClayNS.navier_stokes_vorticity_dt_scaling_exponent
#print axioms FeffermanClayNS.navier_stokes_scaling_homogeneity_deg6
#print axioms FeffermanClayNS.unnormalized_quartic_scaling_mismatch
#print axioms FeffermanClayNS.unmodified_max_rate_of_cubic_source
#print axioms FeffermanClayNS.first_remaining_gap_bochner_polar_damping_at_max
#print axioms FeffermanClayNS.viscous_direction_dissipation_bridge
#print axioms FeffermanClayNS.scale_invariant_cubic_rate_of_direction_coercivity
#print axioms FeffermanClayNS.comparison_ode_ceiling
#print axioms FeffermanClayNS.periodicTetherClosingBound_of_directionDepletion
#print axioms FeffermanClayNS.clay_B_exact_of_periodic_tether_bound
#print axioms FeffermanClayNS.periodicFiniteTimeVorticityBound_of_uniform
#print axioms FeffermanClayNS.periodicBKMContinuation_of_finiteTime
#print axioms FeffermanClayNS.clay_B_exact_of_periodic_finite_time_bound
#print axioms FeffermanClayNS.clay_B_exact_of_torus_direction_depletion
#print axioms FeffermanClayNS.fefferman_periodic_ns_exact_reduction_product_theorem
#print axioms FeffermanClayNS.unitCube_nonempty
#print axioms FeffermanClayNS.bddAbove_range_norm_of_attained_max
#print axioms FeffermanClayNS.vorticity_sup_norm_eq_of_isSpatialMax
#print axioms FeffermanClayNS.polar_pythagoras_directional_deriv
#print axioms FeffermanClayNS.polar_pythagoras_3d_sum
#print axioms FeffermanClayNS.bochner_laplacian_3d_identity
#print axioms FeffermanClayNS.concrete_bochner_polar_viscous_damping_at_max
#print axioms FeffermanClayNS.constVelocity_ne_zero
#print axioms FeffermanClayNS.constVelocity_isPeriodicSmoothInitialData
#print axioms FeffermanClayNS.constVelocity_isPeriodicSmoothSolution
#print axioms FeffermanClayNS.nonzero_periodic_smooth_solution_exists
#print axioms FeffermanClayNS.beltrami_lamb_vector_cross3_zero
#print axioms FeffermanClayNS.beltrami_amplitude_pos_and_bounded
#print axioms FeffermanClayNS.near_field_stretching_absorbed_by_viscous_direction_damping
#print axioms FeffermanClayNS.constantin_fefferman_near_far_cutoff_bridge

-- Main Theorem (reduction) and Stage 6 calculus derivations
#print axioms FeffermanClayNS.clay_reduces_to_direction_curvature_bound
#print axioms Stage6.unit_direction_deriv_orthogonal
#print axioms Stage6.polar_pythagoras_of_hasDerivAt
#print axioms Stage6.bochner_leibniz_of_hasDerivAt
#print axioms Stage6.shearU_heat
#print axioms Stage6.shearV_heat
#print axioms Stage6.shear_beltrami
#print axioms Stage6.shear_nonconstant
#print axioms FeffermanClayNS.clay_B_exact_of_hasDirectionCurvatureCoercivity
#print axioms FeffermanClayNS.HasDirectionCurvatureCoercivity.clay_B_exact
#print axioms Stage6.inner_eq_zero_of_hasDerivAt_of_norm_eq_one
#print axioms Stage6.norm_polar_deriv_sq_eq_of_hasDerivAt
#print axioms Stage6.hasDerivAt_inner_self_deriv_of_hasDerivAt
#print axioms Stage6.isShearBeltramiMode
