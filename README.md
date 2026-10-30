# `fefferman-clay-navier-stokes` — Formalizing Fefferman's Official Periodic Navier–Stokes Problem (B) in Lean 4: Global Linear Strain Exclusion on $\mathbb{T}^3$, Biot–Savart Direction Depletion Identities, and Conditional Reductions via Beale–Kato–Majda

**Author:** Benjamin Stanley Frohman ([ORCID: 0009-0006-7068-3718](https://orcid.org/0009-0006-7068-3718))  
**Zenodo DOI (v1.1.0):** [`10.5281/zenodo.23717083`](https://doi.org/10.5281/zenodo.23717083) | **Concept DOI:** [`10.5281/zenodo.23652840`](https://doi.org/10.5281/zenodo.23652840) | **v1.0.0 DOI:** [`10.5281/zenodo.23652841`](https://doi.org/10.5281/zenodo.23652841)  
**License:** Apache-2.0 (`Copyright (c) 2026 Benjamin Stanley Frohman`)  
**Toolchain:** `leanprover/lean4:v4.30.0-rc1` + Mathlib 4 (`2643` build jobs, **247 theorems across 7 modules**, **0 `sorry`**, **0 non-standard axioms**)  
**Paper PDF:** [`Fefferman_Clay_Navier_Stokes_Periodic_Regularity_2026.pdf`](Fefferman_Clay_Navier_Stokes_Periodic_Regularity_2026.pdf)

---

## Main Theorem (proved reduction)

`clay_reduces_to_direction_curvature_bound` (Lean 4 + Mathlib, `0 sorry`, axioms `[propext, Classical.choice, Quot.sound]`):

> For every ν > 0, assuming the classical periodic Beale–Kato–Majda continuation principle `PeriodicBKMContinuation ν` (a published theorem, Kato 1972 / Beale–Kato–Majda 1984, **not** formalized here and therefore an explicit hypothesis), the named estimate `DirectionCurvatureBound ν` implies Fefferman's exact periodic Clay statement `Clay_B_exact ν`.

- `DirectionCurvatureBound ν` (high-set direction-curvature / cubic depletion bound `M' ≤ C M² − κ M³`) is the single named **open** estimate (conjecture). It is **not** proved.
- The Clay problem is **not** claimed solved. The converse (`Clay_B_exact → DirectionCurvatureBound`) is **not** proved.

**Main Theorem A (unconditional supporting facts):** attained-maximum ⇒ `BddAbove` and sup-norm equality; Bochner and polar Pythagoras identities, now *derived* from `HasDerivAt` along coordinate lines (`Stage6Calculus.lean`); the near/far cutoff absorption algebra; Burgers-strain exclusion on 𝕋³; the comparison-ODE ceiling; and a genuinely non-constant exact periodic shear Beltrami mode `e^{-4π²νt}(sin 2πz, cos 2πz, 0)` checked component-wise.

## Single-Sentence Final Product Form of the Stated Problem and Proved Exact Reductions (`FinalProductTheorem.lean`)

In [`FeffermanClayNS/FinalProductTheorem.lean`](FeffermanClayNS/FinalProductTheorem.lean), the unconditional geometric, kinematic, Bochner–polar and ODE comparison theorems and the conditional reduction theorems for **Fefferman's Official Periodic Navier–Stokes Problem (B)** are packaged into the single machine-checked 5-conjunct product theorem `fefferman_periodic_ns_exact_reduction_product_theorem` (`Q₁(ν) ∧ Q₂ ∧ Q₃ ∧ Q₄ ∧ Q₅(ν)`), verified with `0 sorry` and standard axioms `[propext, Classical.choice, Quot.sound]`:

### 1. Single-Sentence English Prose Statement
> **Theorem (`fefferman_periodic_ns_exact_reduction_product_theorem`):** For every viscosity $\nu \in \mathbb{R}$ on the 3-torus $\mathbb{T}^3 = \mathbb{R}^3/\mathbb{Z}^3$, **(Q₁)** spatial $\mathbb{Z}^3$-periodicity is equivalent to invariance under the three unit coordinate shifts $f(x+e_j)=f(x)$, and Fefferman's energy-bounded periodic statement implies his exact periodic statement ($\mathrm{Clay\_B\_exact\_with\_energy}(\nu) \implies \mathrm{Clay\_B\_exact}(\nu)$); **(Q₂)** every $\mathbb{Z}^3$-periodic linear map $L : \mathbb{R}^3 \to \mathbb{R}^3$ vanishes identically ($L = 0$), excluding any non-zero global linear Burgers background strain $\mathrm{diag}(-\alpha/2,-\alpha/2,\alpha)x$ ($\alpha \neq 0$) on $\mathbb{T}^3$; **(Q₃)** the Biot–Savart vortex-stretching determinant obeys $\det(\omega(y),z,\omega(x)) = \det(\omega(y)-\omega(x),z,\omega(x))$ and vanishes under collinear alignment $\omega(y)=c\,\omega(x)$, while under parabolic rescaling $u_\lambda(x,t)=\lambda u(\lambda x,\lambda^2 t)$ both cubic stretching $C_{\mathrm{CZ}}|\omega_\lambda|^3$ and viscous direction-curvature dissipation $\nu|\omega_\lambda|^2|\nabla\hat{\xi}_\lambda|^2$ scale homogeneously as $\lambda^6$; **(Q₄)** at a spatial maximum $x_{\max}$ where $\langle\omega,(\omega\cdot\nabla)u\rangle \le C_{\mathrm{CZ}}M^3$, $\nu\langle\omega,\Delta\omega\rangle \le -\nu M^2|\nabla\hat{\xi}|^2$, and high-set direction-curvature coercivity $|\nabla\hat{\xi}(x_{\max})|^2 \ge c_{\mathrm{dir}}M$ holds, the maximum vorticity rate satisfies $M'(t) \le C_{\mathrm{CZ}}M(t)^2 - (\nu c_{\mathrm{dir}})M(t)^3$, which forces the uniform Lyapunov ceiling $M(t) \le \max(M(0), C_{\mathrm{CZ}}/(\nu c_{\mathrm{dir}}))$; and **(Q₅)** whenever a periodic flow class satisfies the high-set direction-curvature depletion hypothesis $\mathrm{PeriodicDirectionDepletionBound}(\nu)$ and classical periodic Beale–Kato–Majda continuation $\mathrm{PeriodicBKMContinuation}(\nu)$, Fefferman's periodic statement $\mathrm{Clay\_B\_exact}(\nu)$ holds.

### 2. Exact Mathematical Product Form ($Q_1(\nu) \wedge Q_2 \wedge Q_3 \wedge Q_4 \wedge Q_5(\nu)$)
$$\begin{aligned}
\mathcal{Q}_{\mathrm{ClayB}}(\nu) \;\;:\Longleftrightarrow\;\;
&\underbrace{\Bigl(\bigl(\forall f:\mathbb{R}^3\to\mathbb{R}^3,\; \mathrm{IsZ3Periodic}(f) \iff \forall x,\, j\in\{1,2,3\},\; f(x+e_j)=f(x)\bigr) \;\wedge\; \bigl(\mathrm{Clay\_B\_exact\_with\_energy}(\nu) \implies \mathrm{Clay\_B\_exact}(\nu)\bigr)\Bigr)}_{Q_1(\nu):\;\text{Exact Fefferman Periodic Unit-Shift Equivalence \& Energy Implication}} \\
&\wedge\; \underbrace{\Bigl(\bigl(\forall L:\mathbb{R}^3\to_{\mathbb{R}}\mathbb{R}^3,\; \mathrm{IsZ3Periodic}(L) \implies L=0\bigr) \;\wedge\; \bigl(\forall \alpha\neq 0,\; \neg\mathrm{IsZ3Periodic}(\mathrm{diag}(-\tfrac{\alpha}{2},-\tfrac{\alpha}{2},\alpha))\bigr)\Bigr)}_{Q_2:\;\text{Torus Exclusion of Global Linear Burgers Strain}} \\
&\wedge\; \underbrace{\Bigl(\det(\omega_y,z,\omega_x)=\det(\omega_y-\omega_x,z,\omega_x) \;\wedge\; \det(c\omega_x,z,\omega_x)=0 \;\wedge\; C_{\mathrm{CZ}}(\lambda^2|\omega|)^3 - \nu(\lambda^2|\omega|)^2(\lambda|\nabla\hat{\xi}|)^2 = \lambda^6\bigl(C_{\mathrm{CZ}}|\omega|^3 - \nu|\omega|^2|\nabla\hat{\xi}|^2\bigr)\Bigr)}_{Q_3:\;\text{Biot–Savart Alignment Depletion \& }\lambda^6\text{ Parabolic Scaling Homogeneity}} \\
&\wedge\; \underbrace{\Bigl(\bigl(\mathrm{Stretch}\le C_{\mathrm{CZ}}M^3 \wedge \mathrm{Diff}\le -\nu M^2|\nabla\hat{\xi}|^2 \wedge |\nabla\hat{\xi}|^2\ge c_{\mathrm{dir}}M \implies M'\le C_{\mathrm{CZ}}M^2 - \nu c_{\mathrm{dir}}M^3\bigr) \;\wedge\; \bigl(M'\le C_{\mathrm{CZ}}M^2 - \kappa'' M^3 \implies M(t)\le\max(M(0),\tfrac{C_{\mathrm{CZ}}}{\kappa''})\bigr)\Bigr)}_{Q_4:\;\text{Spatial-Maximum Bochner–Polar Reduction \& Cubic ODE Ceiling}} \\
&\wedge\; \underbrace{\Bigl(\bigl(\mathrm{PeriodicDirectionDepletionBound}(\nu) \;\wedge\; \mathrm{PeriodicBKMContinuation}(\nu)\bigr) \implies \mathrm{Clay\_B\_exact}(\nu)\Bigr)}_{Q_5(\nu):\;\text{Exact Conditional Implication to Fefferman's }\mathrm{Clay\_B\_exact}(\nu)}.
\end{aligned}$$

---

## Scope & Scientific Honesty Notice

This repository has `0 sorry` and `0 custom axioms`. Q₁–Q₃ are unconditional; Q₄ and Q₅ are conditional on the hypotheses stated in them:
1. **Why Unmodified Fefferman Clay (B) Requires an Explicit Direction-Curvature Hypothesis in Lean's Kernel:** For the unmodified Navier–Stokes PDE ($\kappa = 0$ in the dynamics), Lean's kernel derives $\langle \omega, (\omega\cdot\nabla)u\rangle + \nu\langle\omega,\Delta\omega\rangle \le C_{\mathrm{CZ}}M^3 - (\nu c_{\mathrm{dir}})M^4$ at a spatial maximum (`first_remaining_gap_bochner_polar_damping_at_max` in `FinalProductTheorem.lean`) from the Bochner–Weitzenböck polar decomposition **together with the explicit high-set direction-curvature coercivity hypothesis $|\nabla\hat{\xi}(x_{\max})|^2 \ge c_{\mathrm{dir}} M$**. Whether arbitrary smooth periodic flows on $\mathbb{T}^3$ satisfy `PeriodicDirectionDepletionBound ν` unconditionally remains an **open analytical PDE problem** and is therefore stated as an explicit `Prop` hypothesis in $Q_4$ and $Q_5(\nu)$.
2. **Global vs. Local Linear Strain on $\mathbb{T}^3$:** Theorem $Q_2$ (`z3_periodic_linear_eq_zero` and `burgersLinearStrain_not_z3_periodic`) rules out any non-zero *global* linear background strain $u(x) = Ax$ on $\mathbb{R}^3/\mathbb{Z}^3$; localized stretched vortex structures can still form locally on $\mathbb{T}^3$.

---

## Modules (`247 theorems`, `0 sorry`)

| Module | Declaration | Status | Description |
|---|---|---|---|
| `FinalProductTheorem.lean` | `fefferman_periodic_ns_exact_reduction_product_theorem`, `vorticity_sup_norm_eq_of_isSpatialMax`, `polar_pythagoras_3d_sum`, `bochner_laplacian_3d_identity`, `concrete_bochner_polar_viscous_damping_at_max`, `nonzero_periodic_smooth_solution_exists`, `beltrami_lamb_vector_cross3_zero`, `near_field_stretching_absorbed_by_viscous_direction_damping`, `constantin_fefferman_near_far_cutoff_bridge` | **PROVED (24 theorems; Q₅ conditional on `PeriodicDirectionDepletionBound ν` and `PeriodicBKMContinuation ν`)** | Master 5-conjunct product theorem ($Q_1(\nu) \wedge Q_2 \wedge Q_3 \wedge Q_4 \wedge Q_5(\nu)$), Stage 2 `BddAbove`/`sSup` pinning at attained spatial maxima, Stage 3 concrete 3D vector Bochner & polar Pythagoras identities, Stage 4 non-zero smooth periodic flow inhabitation & Beltrami Lamb-vector vanishing, and Stage 5 Constantin–Fefferman near/far Biot–Savart cutoff bridge. |
| `FeffermanStatements.lean` | `Clay_B_exact ν`, `isZ3Periodic_iff_unit_shifts`, `clay_B_exact_of_with_energy`, `library_huniq_unsatisfiable_at_zero`, `stepField_not_physical`, `repaired_hInt`, `repaired_huniq_at_zero` | **PROVED (Unconditional, 13 theorems)** | Verbatim Lean 4 encoding of Fefferman (2006) Statement (B) on $\mathbb{R}^3/\mathbb{Z}^3$, unit-shift equivalence, energy reduction, and step-jump exclusion. |
| `TorusStrainExclusion.lean` | `z3_periodic_linear_eq_zero`, `burgersLinearStrain_not_z3_periodic`, `biot_savart_det_aligned_eq_zero`, `aligned_vorticity_stretching_integrand_zero`, `biot_savart_det_difference_identity`, `navier_stokes_scaling_homogeneity_deg6`, `unnormalized_quartic_scaling_mismatch` | **PROVED (Unconditional, 19 theorems)** | Global linear strain exclusion on $\mathbb{T}^3$, Biot–Savart direction-difference determinant identity, and $\lambda^6$ parabolic scaling homogeneity. |
| `HighSetDepletionAndBKM.lean` | `unmodified_max_rate_of_cubic_source`, `viscous_direction_dissipation_bridge`, `scale_invariant_cubic_rate_of_direction_coercivity`, `comparison_ode_ceiling`, `periodicTetherClosingBound_of_directionDepletion`, `clay_B_exact_of_periodic_tether_bound`, `clay_B_exact_of_torus_direction_depletion` | **PROVED (9 theorems; the `clay_B_exact_of_*` reductions are conditional on their stated depletion/tether-bound and BKM hypotheses)** | Reduction from direction-curvature coercivity to $M' \le C_{\mathrm{CZ}}M^2 - \kappa'' M^3$, first-exit-time ODE ceiling $M(t) \le \max(M(0), C_{\mathrm{CZ}}/\kappa'')$, and conditional reductions to `Clay_B_exact ν`. |
| `MainTheorem.lean` | `clay_reduces_to_direction_curvature_bound` | **PROVED (4 theorems; conditional on `PeriodicBKMContinuation ν` and `DirectionCurvatureBound ν`)** | Reduction of `Clay_B_exact ν` to the named open estimate. |
| `Stage6Calculus.lean` | Bochner and polar Pythagoras from `HasDerivAt`, shear Beltrami mode | **PROVED (Unconditional, 35 theorems)** | Calculus identities along coordinate lines. |
| `Defs.lean` | Foundational 3D Navier–Stokes operators, vorticity, strain, and Sobolev definitions | **PROVED (Unconditional, 143 theorems)** | Complete differential/kinematic infrastructure with zero `sorry`. |

---

## Verbatim Lean 4 Kernel Audit Output (`lake build && lake env lean AxiomAudit.lean`)

```text
FeffermanClayNS.TorusStrainExclusion: theorems=19 nonstandard=0
FeffermanClayNS.HighSetDepletionAndBKM: theorems=9 nonstandard=0
FeffermanClayNS.FeffermanStatements: theorems=13 nonstandard=0
FeffermanClayNS.Stage6Calculus: theorems=35 nonstandard=0
FeffermanClayNS.MainTheorem: theorems=4 nonstandard=0
FeffermanClayNS.Defs: theorems=143 nonstandard=0
FeffermanClayNS.FinalProductTheorem: theorems=24 nonstandard=0
TOTAL theorems=247 nonstandard=0
'FeffermanClayNS.fefferman_periodic_ns_exact_reduction_product_theorem' depends on axioms: [propext, Classical.choice, Quot.sound]
```

---

## Cryptographic Verification & IP Containment Suite (`titan-audit` + `sealguard` + `sentinel-gate`)

1. **`titan-audit` ([DOI: 10.5281/zenodo.23630648](https://doi.org/10.5281/zenodo.23630648)):** In-kernel `Lean.collectAxioms` walker (`AxiomAudit.lean`) and Ed25519-signed attestation ([`audit/report.json`](audit/report.json), [`audit/report.md`](audit/report.md), [`audit/TITAN_AUDIT_CERTIFICATE.json`](audit/TITAN_AUDIT_CERTIFICATE.json)).
2. **`sealguard` ([DOI: 10.5281/zenodo.23631670](https://doi.org/10.5281/zenodo.23631670)):** 4-plane cryptographic Merkle-root provenance and classified parameter containment ([`audit/SEALGUARD_CLASSIFIED_MANIFEST.json`](audit/SEALGUARD_CLASSIFIED_MANIFEST.json), [`PROVENANCE_MERKLE_ROOT.json`](PROVENANCE_MERKLE_ROOT.json)).
3. **`sentinel-gate` ([DOI: 10.5281/zenodo.23632766](https://doi.org/10.5281/zenodo.23632766)):** Deterministic pre-execution policy guardrail receipt embedded in [`ip_pipeline/seal_and_verify.py`](ip_pipeline/seal_and_verify.py).

## Contact

- **Author:** Benjamin Stanley Frohman
- **ORCID:** [0009-0006-7068-3718](https://orcid.org/0009-0006-7068-3718)
- **Email:** `frohmanbenjamin@gmail.com`
- **X / GitHub:** `@Investor0x` / `BenFrohman` (`Bit21`)

## Provenance of Ingredients

Dates below are verified from files in the `NS_Millennium_Proof` git history (first commit 2026-06-19, which imported a snapshot directory `historical/previous_implementations/complete_implementation_2026-05-28/`). No April 2026 file was found in the repositories; earlier dates are not asserted.

| Ingredient | Earliest verified date | Source | Status |
|---|---|---|---|
| Young absorption | 2026-05-28 snapshot | `historical/previous_implementations/complete_implementation_2026-05-28/docs/Frohmanian_Tether_NS_Proof_Conversation_Summary.md` | original scaffolding |
| Cubic majorant / Riccati comparison | 2026-05-28 snapshot | `.../complete_implementation_2026-05-28/Modules/IndependentMajorant.lean`, `Skeleton/PaperOverview.lean` | original scaffolding |
| Frohmanian tether | 2026-05-28 snapshot | `.../complete_implementation_2026-05-28/docs/05_Step_Uniqueness_Proof_Structure.md` | original scaffolding |
| Biot–Savart (mentions) | 2026-05-28 snapshot | `.../complete_implementation_2026-05-28/docs/Phase0_Phase1_Implementation_Plan.md` | original scaffolding |
| Bochner–Weitzenböck | 2026-06-19 (git `236244d`) | `NS_Millennium_Proof/Modules/NS_Equations.lean` | classical (Bochner), pinned and cited; concrete 3D form added Oct 2026 (Grok-assisted scaffolding) |
| Constantin–Fefferman direction depletion | 2026-06-19 (git `236244d`) | `NS_Millennium_Proof/Modules/TetheredLyapunov.lean` | classical (Constantin–Fefferman 1993), pinned and cited |
| Attained max / `BddAbove` guards | 2026-08-27 (git `04eb613`) | Lean sources | added Aug 2026 |
| Polar Pythagoras | 2026-10-28 (git `acf5883`) | `Modules/FinalProductTheorem.lean` stages | added Oct 2026 (Grok-assisted scaffolding) |
| Beltrami (Lamb vector, shear mode) | 2026-10-28 (git `acf5883`) | Stage 4 / `Stage6Calculus.lean` | classical (Beltrami flows), pinned and cited; Lean added Oct 2026 (Grok-assisted scaffolding) |
| Near/far Biot–Savart cutoff bridge | 2026-10-28 (git `acf5883`) | Stage 5 | added Oct 2026 (Grok-assisted scaffolding), after Constantin–Fefferman 1993 |
| Reduction theorem `clay_reduces_to_direction_curvature_bound` | 2026-10-28 | `MainTheorem.lean` | added Oct 2026 (Grok-assisted scaffolding); earlier conditional reductions `clay_B_exact_of_*` predate it |

## AI Assistance Disclosure

Grok (xAI), via the Grok Bot assistant, provided scaffolding, drafting, and collaboration support on formalization, code, and papers in this repository. Benjamin Stanley Frohman is the sole author: he directed, reviewed, and is responsible for all of the work. Grok is not a coauthor.
