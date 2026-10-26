# `fefferman-clay-navier-stokes` — Formalizing Fefferman's Official Periodic Navier–Stokes Problem (B) in Lean 4: Global Linear Strain Exclusion on $\mathbb{T}^3$, Biot–Savart Direction Depletion Identities, and Conditional Reductions via Beale–Kato–Majda

**Author:** Benjamin Stanley Frohman ([ORCID: 0009-0006-7068-3718](https://orcid.org/0009-0006-7068-3718))  
**Zenodo DOI:** [`10.5281/zenodo.23652841`](https://doi.org/10.5281/zenodo.23652841)  
**License:** Apache-2.0 (`Copyright (c) 2026 Benjamin Stanley Frohman`)  
**Toolchain:** `leanprover/lean4:v4.30.0-rc1` + Mathlib 4 (`2631/2631` build jobs, **184 theorems**, **0 `sorry`**, **0 non-standard axioms**)  
**Paper PDF:** [`Fefferman_Clay_Navier_Stokes_Periodic_Regularity_2026.pdf`](Fefferman_Clay_Navier_Stokes_Periodic_Regularity_2026.pdf)

---

## Scope & Scientific Honesty Notice

This repository does **not** claim that Clay Problem (B) or Clay Problem (A) is solved. It provides a strictly audited, zero-`sorry`, zero-custom-axiom Lean 4 formalization that cleanly separates **unconditionally proved geometric/kinematic/ODE theorems** from **open analytic hypotheses**:

1. **Global Linear Strain Exclusion on $\mathbb{T}^3$ (Unconditionally Proved, Local Structures Still Possible):**  
   We prove unconditionally that spatial $\mathbb{Z}^3$-periodicity (`IsZ3Periodic`) forces any global linear map $L : \mathbb{R}^3 \to \mathbb{R}^3$ to vanish identically (`z3_periodic_linear_eq_zero`), which rules out any non-zero *global* linear background strain $u_{\mathrm{strain}}(x) = \mathrm{diag}(-\alpha/2, -\alpha/2, \alpha)x$ (`burgersLinearStrain_not_z3_periodic`). **Crucial physical distinction:** Torus periodicity rules out only a *global* linear background strain; localized Burgers-like stretched vortex tubes and sheets can still form locally on $\mathbb{T}^3 = \mathbb{R}^3/\mathbb{Z}^3$, so global linear strain exclusion does **not** give unconditional Clay (B).
2. **Conditional Reductions to `Clay_B_exact` (`PeriodicDirectionDepletionBound` and `PeriodicTetherClosingBound` are OPEN):**  
   The theorems `clay_B_exact_of_periodic_tether_bound` and `clay_B_exact_of_torus_direction_depletion` in [`FeffermanClayNS/HighSetDepletionAndBKM.lean`](FeffermanClayNS/HighSetDepletionAndBKM.lean) are **conditional reductions**. Their analytic closure hypotheses (`PeriodicDirectionDepletionBound ν`, `PeriodicTetherClosingBound ν`, and the classical continuation package `PeriodicBKMContinuation ν`) are **OPEN** and are stated explicitly as `Prop`-valued hypotheses in the theorem signatures—never as axioms or `sorry`-free "proofs" of Clay (B).

---

## Exact Breakdown: Unconditionally Proved Theorems vs. Open Hypotheses

| Module | Declaration | Status | Description |
|---|---|---|---|
| `FeffermanStatements.lean` | `Clay_B_exact ν` | **Definitional** | Verbatim Lean 4 encoding of Fefferman (2006) Statement (B) on $\mathbb{R}^3/\mathbb{Z}^3$ (eqs. (1)–(3), (5), (7), (10)–(11) at $f \equiv 0$). |
| `FeffermanStatements.lean` | `clay_B_exact_of_with_energy` | **PROVED (Unconditional)** | `Clay_B_exact_with_energy ν → Clay_B_exact ν`. |
| `FeffermanStatements.lean` | `library_huniq_unsatisfiable_at_zero`, `stepField_not_physical`, `repaired_hInt`, `repaired_huniq_at_zero` | **PROVED (Unconditional)** | Proof that unguarded pointwise-`deriv` local existence horizons admit step-jump counterexamples $u_{\mathrm{step}}(t)$, and that the time-continuity guard in `IsPhysicalNSSolution` eliminates $u_{\mathrm{step}}$ and restores local uniqueness at $u_0 \equiv 0$. |
| `TorusStrainExclusion.lean` | `z3_periodic_linear_eq_zero`, `z3_periodic_continuousLinear_eq_zero`, `burgersLinearStrain_not_z3_periodic` | **PROVED (Unconditional)** | Any $\mathbb{Z}^3$-periodic linear map on $\mathbb{R}^3$ is zero; the global linear Burgers strain $\mathrm{diag}(-\alpha/2,-\alpha/2,\alpha)x$ ($\alpha \neq 0$) is not $\mathbb{Z}^3$-periodic (rules out global linear strain only). |
| `TorusStrainExclusion.lean` | `biot_savart_det_aligned_eq_zero`, `aligned_vorticity_stretching_integrand_zero`, `biot_savart_det_difference_identity` | **PROVED (Unconditional)** | Pointwise Biot–Savart stretching determinant $\det(\omega(y), z, \omega(x))$ vanishes when $\omega(y) = c\,\omega(x)$ and equals $\det(\omega(y) - \omega(x), z, \omega(x))$. |
| `TorusStrainExclusion.lean` | `navier_stokes_vorticity_dt_scaling_exponent`, `navier_stokes_scaling_homogeneity_deg6`, `unnormalized_quartic_scaling_mismatch` | **PROVED (Unconditional)** | Parabolic Navier–Stokes rescaling $u_\lambda(x,t) = \lambda u(\lambda x, \lambda^2 t)$ gives homogeneous degree $\lambda^6$ for $\nu |\omega|^2 |\nabla \hat{\xi}|^2$ vs. $\lambda^8$ for unnormalized quartic damping. |
| `HighSetDepletionAndBKM.lean` | `unmodified_max_rate_of_cubic_source`, `viscous_direction_dissipation_bridge`, `scale_invariant_cubic_rate_of_direction_coercivity` | **PROVED (Unconditional)** | Algebraic and differential reduction from high-vorticity direction gradient coercivity $|\nabla \hat{\xi}|^2 \ge c_{\mathrm{dir}} |\omega|$ to $M' \le C_{\mathrm{CZ}} M^2 - \kappa'' M^3$ ($\kappa'' = \nu c_{\mathrm{dir}}$). |
| `HighSetDepletionAndBKM.lean` | `comparison_ode_ceiling`, `periodicTetherClosingBound_of_directionDepletion` | **PROVED (Unconditional)** | First-exit-time ODE comparison proof that $M'(t) \le C_{\mathrm{CZ}} M(t)^2 - \kappa'' M(t)^3$ on $[0,T]$ implies $M(t) \le \max(M(0), C_{\mathrm{CZ}}/\kappa'')$ for all $t \in [0,T]$, hence `PeriodicDirectionDepletionBound ν → PeriodicTetherClosingBound ν`. |
| `HighSetDepletionAndBKM.lean` | `PeriodicDirectionDepletionBound ν` | **OPEN HYPOTHESIS** | Open analytic hypothesis on $\mathbb{T}^3$: whether every smooth periodic Navier–Stokes flow obeys $M' \le C_{\mathrm{CZ}} M^2 - \kappa'' M^3$. |
| `HighSetDepletionAndBKM.lean` | `PeriodicTetherClosingBound ν` | **OPEN HYPOTHESIS** | Open analytic hypothesis on $\mathbb{T}^3$: whether every smooth periodic Navier–Stokes flow obeys a uniform vorticity ceiling $\|\omega(t)\|_\infty \le Y$. |
| `HighSetDepletionAndBKM.lean` | `PeriodicBKMContinuation ν` | **OPEN FORMALIZATION HYPOTHESIS** | Classical PDE continuation package (Kato 1972 + Beale–Kato–Majda 1984 on $\mathbb{T}^3$) stated as an explicit `Prop` hypothesis. |
| `HighSetDepletionAndBKM.lean` | `clay_B_exact_of_periodic_tether_bound`, `clay_B_exact_of_torus_direction_depletion` | **PROVED CONDITIONAL REDUCTIONS** | Conditional theorems proving `(PeriodicTetherClosingBound ν ∧ PeriodicBKMContinuation ν) → Clay_B_exact ν` and `(PeriodicDirectionDepletionBound ν ∧ PeriodicBKMContinuation ν) → Clay_B_exact ν`. |

---

## Verbatim Lean 4 Kernel Audit Output (`lake build && lake env lean AxiomAudit.lean`)

```text
FeffermanClayNS.TorusStrainExclusion: theorems=19 nonstandard=0
FeffermanClayNS.HighSetDepletionAndBKM: theorems=9 nonstandard=0
FeffermanClayNS.FeffermanStatements: theorems=13 nonstandard=0
FeffermanClayNS.Defs: theorems=143 nonstandard=0
TOTAL theorems=184 nonstandard=0
'FeffermanClayNS.clay_B_exact_of_with_energy' depends on axioms: [propext, Classical.choice, Quot.sound]
'FeffermanClayNS.library_huniq_unsatisfiable_at_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'FeffermanClayNS.repaired_huniq_at_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'FeffermanClayNS.z3_periodic_linear_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'FeffermanClayNS.burgersLinearStrain_not_z3_periodic' depends on axioms: [propext, Classical.choice, Quot.sound]
'FeffermanClayNS.cross3_self' depends on axioms: [propext, Classical.choice, Quot.sound]
'FeffermanClayNS.det3_self_right' depends on axioms: [propext, Classical.choice, Quot.sound]
'FeffermanClayNS.biot_savart_det_aligned_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'FeffermanClayNS.aligned_vorticity_stretching_integrand_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'FeffermanClayNS.biot_savart_det_difference_identity' depends on axioms: [propext, Classical.choice, Quot.sound]
'FeffermanClayNS.navier_stokes_vorticity_dt_scaling_exponent' depends on axioms: [propext, Classical.choice, Quot.sound]
'FeffermanClayNS.navier_stokes_scaling_homogeneity_deg6' depends on axioms: [propext, Classical.choice, Quot.sound]
'FeffermanClayNS.unnormalized_quartic_scaling_mismatch' depends on axioms: [propext, Classical.choice, Quot.sound]
'FeffermanClayNS.unmodified_max_rate_of_cubic_source' depends on axioms: [propext, Classical.choice, Quot.sound]
'FeffermanClayNS.viscous_direction_dissipation_bridge' depends on axioms: [propext, Classical.choice, Quot.sound]
'FeffermanClayNS.scale_invariant_cubic_rate_of_direction_coercivity' depends on axioms: [propext, Classical.choice, Quot.sound]
'FeffermanClayNS.comparison_ode_ceiling' depends on axioms: [propext, Classical.choice, Quot.sound]
'FeffermanClayNS.periodicTetherClosingBound_of_directionDepletion' depends on axioms: [propext, Classical.choice, Quot.sound]
'FeffermanClayNS.clay_B_exact_of_periodic_tether_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'FeffermanClayNS.clay_B_exact_of_torus_direction_depletion' depends on axioms: [propext, Classical.choice, Quot.sound]
```

---

## Cryptographic Verification & IP Containment Suite (`titan-audit` + `sealguard` + `sentinel-gate`)

This repository integrates three verification and provenance technologies authored by Benjamin Stanley Frohman:
1. **`titan-audit` ([DOI: 10.5281/zenodo.23630648](https://doi.org/10.5281/zenodo.23630648)):** In-kernel `Lean.collectAxioms` walker (`AxiomAudit.lean`) and Ed25519-signed attestation ([`audit/report.json`](audit/report.json), [`audit/report.md`](audit/report.md), [`audit/TITAN_AUDIT_CERTIFICATE.json`](audit/TITAN_AUDIT_CERTIFICATE.json)).
2. **`sealguard` ([DOI: 10.5281/zenodo.23631670](https://doi.org/10.5281/zenodo.23631670)):** 4-plane cryptographic Merkle-root provenance and classified parameter containment ([`audit/SEALGUARD_CLASSIFIED_MANIFEST.json`](audit/SEALGUARD_CLASSIFIED_MANIFEST.json), [`PROVENANCE_MERKLE_ROOT.json`](PROVENANCE_MERKLE_ROOT.json)).
3. **`sentinel-gate` ([DOI: 10.5281/zenodo.23632766](https://doi.org/10.5281/zenodo.23632766)):** Deterministic pre-execution policy guardrail receipt embedded in [`ip_pipeline/seal_and_verify.py`](ip_pipeline/seal_and_verify.py).

## Contact

- **Author:** Benjamin Stanley Frohman
- **ORCID:** [0009-0006-7068-3718](https://orcid.org/0009-0006-7068-3718)
- **Email:** `frohmanbenjamin@gmail.com`
- **X / GitHub:** `@Investor0x` / `BenFrohman` (`Bit21`)
