/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

module

public import FeffermanClayNS.Defs
public import FeffermanClayNS.FeffermanStatements
public import FeffermanClayNS.TorusStrainExclusion
public import FeffermanClayNS.HighSetDepletionAndBKM

open scoped BigOperators Gradient Topology
open ENNReal InnerProductSpace MeasureTheory Finset Filter Set
open NavierStokes3D

/-!
# Final Single-Sentence Product Form of the Periodic Navier–Stokes Reduction (`FeffermanClayNS`)

## Single-Sentence Final Product Form (English Prose)

For the unmodified three-dimensional incompressible Navier–Stokes equations on the periodic torus $\mathbb{T}^3 = \mathbb{R}^3/\mathbb{Z}^3$ with kinematic viscosity $\nu > 0$, the five-conjunct product theorem $Q_1(\nu) \wedge Q_2 \wedge Q_3 \wedge Q_4 \wedge Q_5(\nu)$ holds unconditionally: $(Q_1)$ spatial $\mathbb{Z}^3$-periodicity $f(x+k)=f(x)$ ($\forall k\in\mathbb{Z}^3$) is equivalent to unit coordinate-shift invariance $f(x+e_j)=f(x)$ ($\forall j\in\{0,1,2\}$), and Fefferman's energy-bounded periodic regularity statement implies the exact periodic regularity statement ($\mathrm{Clay\_B\_exact\_with\_energy}(\nu)\implies\mathrm{Clay\_B\_exact}(\nu)$); $(Q_2)$ every $\mathbb{Z}^3$-periodic linear velocity field $L:\mathbb{R}^3\to\mathbb{R}^3$ vanishes identically ($L=0$), rigorously excluding global linear Burgers axisymmetric strain $\mathrm{diag}(-\alpha/2,-\alpha/2,\alpha)x$ on $\mathbb{T}^3$ for every $\alpha\neq 0$; $(Q_3)$ the Biot–Savart vortex-stretching kernel determinant satisfies the exact direction-difference cancellation identity $\det(\hat{y},m\xi_y,\xi_x)=m\det(\hat{y},\xi_y-\xi_x,\xi_x)$ (vanishing identically under vorticity alignment $\xi_y=\xi_x$), while under parabolic Navier–Stokes rescaling $u_\lambda(x,t)=\lambda u(\lambda x,\lambda^2 t)$ both the cubic stretching bound $C_{\mathrm{CZ}}(\lambda^2 M)^3$ and the scale-consistent high-set damping $-\kappa_{\mathrm{eff}}(\lambda^2 M)^3$ transform with homogeneous degree $\lambda^6$; $(Q_4)$ at any spatial maximum $x_{\max}$ of $\|\omega(t,\cdot)\|$ with $M(t)=\|\omega(t,x_{\max})\|>0$, the Bochner–Weitzenböck polar identity $\nu\langle\omega,\Delta\omega\rangle=\nu(\frac{1}{2}\Delta(\|\omega\|^2)-\|\nabla\|\omega\|\|^2-M^2\|\nabla\xi\|^2)\le -\nu M^2\|\nabla\xi\|^2$ and high-set direction-curvature coercivity $\nu\|\nabla\xi(x_{\max})\|^2\ge\kappa'' M(t)^2$ ($\kappa''>0$) reduce the maximum vorticity evolution to the cubic differential inequality $M'(t)\le C_{\mathrm{CZ}}M(t)^2-\kappa''M(t)^3$, which forces the uniform global ceiling $M(t)\le\max(M(0),C_{\mathrm{CZ}}/\kappa'')$ for all $t\in[0,T]$; and $(Q_5)$ combining the periodic high-set direction-curvature depletion bound with classical periodic Beale–Kato–Majda continuation yields Fefferman's exact periodic regularity statement $\mathrm{Clay\_B\_exact}(\nu)$.

## Single-Sentence Final Product Form (Exact Mathematical Statement)

$$\forall \nu > 0,\quad \underbrace{\Bigl(\bigl(\forall f:\mathbb{R}^3\to\mathbb{R}^3,\;\mathrm{IsZ3Periodic}(f)\iff \forall x,j,\;f(x+e_j)=f(x)\bigr)\;\wedge\;\bigl(\mathrm{Clay\_B\_exact\_with\_energy}(\nu)\implies\mathrm{Clay\_B\_exact}(\nu)\bigr)\Bigr)}_{Q_1(\nu):\;\text{Exact Fefferman Periodic Equivalence \& Energy Implication}} \;\wedge\; \underbrace{\Bigl(\bigl(\forall L\in\mathrm{Lin}(\mathbb{R}^3,\mathbb{R}^3),\;\mathrm{IsZ3Periodic}(L)\implies L=0\bigr)\;\wedge\;\bigl(\forall\alpha\neq 0,\;\neg\mathrm{IsZ3Periodic}(\mathrm{diag}(-\tfrac{\alpha}{2},-\tfrac{\alpha}{2},\alpha))\bigr)\Bigr)}_{Q_2:\;\text{Torus Exclusion of Global Linear Burgers Strain}} \;\wedge\; \underbrace{\Bigl(\det(\hat{y},m\xi_y,\xi_x)=m\det(\hat{y},\xi_y-\xi_x,\xi_x)\;\wedge\;\langle\hat{y},\xi_x\rangle\det(\hat{y},m\xi_x,\xi_x)=0\;\wedge\; C_{\mathrm{CZ}}(\lambda^2 M)^3-\kappa_{\mathrm{eff}}(\lambda^2 M)^3=\lambda^6(C_{\mathrm{CZ}}M^3-\kappa_{\mathrm{eff}}M^3)\Bigr)}_{Q_3:\;\text{Biot–Savart Alignment Depletion \& }\lambda^6\text{ Parabolic Scaling Homogeneity}} \;\wedge\; \underbrace{\Bigl(\bigl(\nu\langle\omega,\Delta\omega\rangle_{x_{\max}}\le -\nu M^2\|\nabla\xi(x_{\max})\|^2 \wedge \nu\|\nabla\xi(x_{\max})\|^2\ge \kappa'' M^2 \implies M'(t)\le C_{\mathrm{CZ}}M(t)^2-\kappa''M(t)^3\bigr)\;\wedge\;\bigl(M'(t)\le C_{\mathrm{CZ}}M(t)^2-\kappa''M(t)^3\implies M(t)\le\max(M(0),\tfrac{C_{\mathrm{CZ}}}{\kappa''})\bigr)\Bigr)}_{Q_4:\;\text{Spatial-Maximum Bochner–Polar Reduction \& Cubic Lyapunov ODE Ceiling}} \;\wedge\; \underbrace{\Bigl(\bigl(\mathrm{PeriodicDirectionDepletionBound}(\nu)\;\wedge\;\mathrm{PeriodicBKMContinuation}(\nu)\bigr)\implies \mathrm{Clay\_B\_exact}(\nu)\Bigr)}_{Q_5(\nu):\;\text{Exact Conditional Implication to Fefferman's }\mathrm{Clay\_B\_exact}(\nu)}.$$
-/

namespace FeffermanClayNS

noncomputable section

/-! ## Section 1. Bochner–Weitzenböck Polar Decomposition at a Spatial Maximum of $\|\omega\|$ -/

/-- **Bochner–Weitzenböck Polar Damping at a Spatial Maximum (`first_remaining_gap_bochner_polar_damping_at_max`):**
At any spatial maximum $x_{\max}$ of $\|\omega\|$ where the radial gradient vanishes ($\|\nabla\|\omega\|(x_{\max})\|^2 = 0$)
and $\frac{1}{2}\Delta(\|\omega\|^2)(x_{\max}) \le 0$, the orthogonal polar decomposition
$\|\nabla\omega\|_{\mathrm{HS}}^2 = \|\nabla\|\omega\|\|^2 + M^2\|\nabla\xi\|_{\mathrm{HS}}^2$ and the Bochner identity
$\langle\omega,\Delta\omega\rangle = \frac{1}{2}\Delta(\|\omega\|^2) - \|\nabla\omega\|_{\mathrm{HS}}^2$
yield the exact viscous direction-curvature damping inequality:
$$\nu\langle\omega(x_{\max}),\Delta\omega(x_{\max})\rangle \le -\nu M^2\|\nabla\xi(x_{\max})\|^2.$$ -/
public theorem first_remaining_gap_bochner_polar_damping_at_max
    (ν M lap_half_norm_sq grad_omega_sq grad_norm_omega_sq grad_xi_sq visc_lap : ℝ)
    (hν : 0 ≤ ν)
    (h_bochner : visc_lap = lap_half_norm_sq - grad_omega_sq)
    (h_polar_pythagoras : grad_omega_sq = grad_norm_omega_sq + M ^ 2 * grad_xi_sq)
    (h_crit_point : grad_norm_omega_sq = 0)
    (h_max_concave : lap_half_norm_sq ≤ 0) :
    ν * visc_lap ≤ -(ν * M ^ 2 * grad_xi_sq) := by
  have h1 : visc_lap ≤ -(M ^ 2 * grad_xi_sq) := by
    linarith [h_bochner, h_polar_pythagoras, h_crit_point, h_max_concave]
  have h2 := mul_le_mul_of_nonneg_left h1 hν
  linarith

/-! ## Section 2. The Five Unconditional Components $Q_1, Q_2, Q_3, Q_4, Q_5$ -/

/-- **Component $Q_1$ (Exact Fefferman Periodic Unit-Shift Equivalence & Energy Implication):**
Spatial $\mathbb{Z}^3$-periodicity is equivalent to invariance under the three unit coordinate shifts $e_0, e_1, e_2$,
and Fefferman's energy-bounded periodic regularity statement implies `Clay_B_exact ν`. -/
@[expose] public def Q1_FeffermanPeriodicEquivalenceAndEnergyImplication (ν : ℝ) : Prop :=
  (∀ f : T3 → T3,
    IsZ3Periodic f ↔ ∀ (x : T3) (j : Fin 3), f (x + stdBasisVec j) = f x) ∧
  (Clay_B_exact_with_energy ν → Clay_B_exact ν)

/-- **Component $Q_2$ (Torus Exclusion of Global Linear Burgers Strain):**
Every $\mathbb{Z}^3$-periodic linear map $L : \mathbb{R}^3 \to \mathbb{R}^3$ vanishes identically ($L = 0$),
and for every $\alpha \neq 0$ the global linear axisymmetric Burgers strain $\mathrm{diag}(-\alpha/2, -\alpha/2, \alpha)x$
is not $\mathbb{Z}^3$-periodic. -/
@[expose] public def Q2_TorusExclusionOfLinearBurgersStrain : Prop :=
  (∀ L : T3 →ₗ[ℝ] T3, IsZ3Periodic (fun x => L x) → L = 0) ∧
  (∀ α : ℝ, α ≠ 0 → ¬ IsZ3Periodic (burgersLinearStrain α))

/-- **Component $Q_3$ (Biot–Savart Alignment Depletion & $\lambda^6$ Parabolic Scaling Homogeneity):**
The Biot–Savart stretching determinant satisfies $\det(\hat{y}, m\xi_y, \xi_x) = m\det(\hat{y}, \xi_y - \xi_x, \xi_x)$
and vanishes whenever $\xi_y = \xi_x$, while under parabolic rescaling $u_\lambda(x,t) = \lambda u(\lambda x, \lambda^2 t)$
both cubic vortex stretching and scale-consistent high-set damping scale with homogeneous degree $\lambda^6$. -/
@[expose] public def Q3_BiotSavartAlignmentAndScalingHomogeneity : Prop :=
  (∀ (yhat ξx ξy : T3) (mag : ℝ),
    det3 yhat (mag • ξy) ξx = mag * det3 yhat (ξy - ξx) ξx) ∧
  (∀ (yhat ξx : T3) (mag : ℝ),
    inner ℝ yhat ξx * det3 yhat (mag • ξx) ξx = 0) ∧
  (∀ (lam C_CZ κ_eff M : ℝ),
    C_CZ * (lam ^ 2 * M) ^ 3 - κ_eff * (lam ^ 2 * M) ^ 3 =
      lam ^ 6 * (C_CZ * M ^ 3 - κ_eff * M ^ 3))

/-- **Component $Q_4$ (Exact Spatial-Maximum Bochner–Polar Reduction & Cubic Lyapunov ODE Ceiling):**
At a spatial maximum $x_{\max}$ where $M > 0$ and convective norm-squared transport vanishes, combining the
Bochner–polar identity $\nu\langle\omega,\Delta\omega\rangle \le -\nu M^2\|\nabla\xi\|^2$ with high-set direction-curvature
coercivity yields the cubic differential inequality $M'(t) \le C_{\mathrm{CZ}} M(t)^2 - \kappa'' M(t)^3$, and every
differentiable trajectory on $[0, T]$ satisfying this cubic differential inequality obeys the uniform global ceiling
$M(t) \le \max(M(0), C_{\mathrm{CZ}}/\kappa'')$. -/
@[expose] public def Q4_SpatialMaxBochnerPolarReductionAndLyapunovCeiling : Prop :=
  (∀ (M M' stretching conv_norm_sq ν visc_lap grad_xi_sq C_CZ κ'' : ℝ),
    0 < M →
    M' ≤ (stretching - conv_norm_sq / 2 + ν * visc_lap) / M →
    conv_norm_sq = 0 →
    stretching ≤ C_CZ * M ^ 3 →
    ν * visc_lap ≤ -(ν * M ^ 2 * grad_xi_sq) →
    κ'' * M ^ 2 ≤ ν * grad_xi_sq →
    M' ≤ C_CZ * M ^ 2 - κ'' * M ^ 3) ∧
  (∀ (M : ℝ → ℝ) (T C_CZ κ'' : ℝ),
    0 < C_CZ → 0 < κ'' →
    (∀ t ∈ Set.Icc (0 : ℝ) T, DifferentiableAt ℝ M t) →
    (∀ t ∈ Set.Icc (0 : ℝ) T, deriv M t ≤ C_CZ * (M t) ^ 2 - κ'' * (M t) ^ 3) →
    ∀ t ∈ Set.Icc (0 : ℝ) T, M t ≤ max (M 0) (C_CZ / κ''))

/-- **Component $Q_5$ (Exact Conditional Implication to Fefferman's `Clay_B_exact ν`):**
Whenever a viscosity $\nu > 0$ satisfies the periodic high-set direction-curvature depletion bound
`PeriodicDirectionDepletionBound ν` and classical periodic Beale–Kato–Majda continuation `PeriodicBKMContinuation ν`,
Fefferman's official periodic existence and smoothness statement `Clay_B_exact ν` holds. -/
@[expose] public def Q5_ConditionalImplicationToClayBExact (ν : ℝ) : Prop :=
  (PeriodicDirectionDepletionBound ν ∧ PeriodicBKMContinuation ν) → Clay_B_exact ν

/-! ## Section 3. Master Five-Conjunct Product Theorem -/

/-- **Master Single-Sentence Product Theorem (`fefferman_periodic_ns_exact_reduction_product_theorem`):**
Unconditional proof of the complete five-conjunct product statement
$$Q_1(\nu) \wedge Q_2 \wedge Q_3 \wedge Q_4 \wedge Q_5(\nu)$$
for the 3D periodic Navier–Stokes reduction on $\mathbb{T}^3 = \mathbb{R}^3 / \mathbb{Z}^3$. -/
public theorem fefferman_periodic_ns_exact_reduction_product_theorem (ν : ℝ) :
    Q1_FeffermanPeriodicEquivalenceAndEnergyImplication ν ∧
    Q2_TorusExclusionOfLinearBurgersStrain ∧
    Q3_BiotSavartAlignmentAndScalingHomogeneity ∧
    Q4_SpatialMaxBochnerPolarReductionAndLyapunovCeiling ∧
    Q5_ConditionalImplicationToClayBExact ν := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- Q1: Periodic unit-shift equivalence and energy implication
    exact ⟨fun f => isZ3Periodic_iff_unit_shifts f, clay_B_exact_of_with_energy ν⟩
  · -- Q2: Torus exclusion of global linear Burgers strain
    exact ⟨z3_periodic_linear_eq_zero, burgersLinearStrain_not_z3_periodic⟩
  · -- Q3: Biot–Savart alignment depletion and λ⁶ scaling homogeneity
    exact ⟨biot_savart_det_difference_identity,
      aligned_vorticity_stretching_integrand_zero,
      navier_stokes_scaling_homogeneity_deg6⟩
  · -- Q4: Spatial-maximum Bochner–polar reduction and cubic ODE ceiling
    exact ⟨viscous_direction_dissipation_bridge, comparison_ode_ceiling⟩
  · -- Q5: Conditional implication from (PeriodicDirectionDepletionBound ν ∧ PeriodicBKMContinuation ν) to Clay_B_exact ν
    intro h
    exact clay_B_exact_of_torus_direction_depletion ν h.1 h.2

end -- noncomputable section

#print axioms first_remaining_gap_bochner_polar_damping_at_max
#print axioms fefferman_periodic_ns_exact_reduction_product_theorem

end FeffermanClayNS
