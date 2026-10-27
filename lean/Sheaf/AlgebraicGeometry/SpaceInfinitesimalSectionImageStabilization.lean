/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q56
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceIdealPowerQuotients
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.Filtration
import Sheaf.CategoryTheory.ModuleAbelianEvaluationComparison
import WeilConjectures.CategoryTheory.RightDerivedUniversalDeltaFunctor

/-! # Stabilization of images of infinitesimal quotient sections

Source: Stacks Project, Spaces Cohomology, Situation 08AV and Lemma 08AY(3),
at p = 0 and I equal to the maximal ideal
(blueprint: lem-sfb-space-infinitesimal-section-image-stabilization).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- For a line module on a proper algebraic space over a Noetherian local ring,
the images of sections of sufficiently deep ideal-power quotients equal the image
of sections of the original module. No completeness or flatness is assumed.
Source: Stacks Project, Situation 08AV and Lemma 08AY(3), p = 0 and I = m
(blueprint: lem-sfb-space-infinitesimal-section-image-stabilization).

Proof (the accepted DAG split):
1. For every etale scheme chart $U\to Z$, its composite with $g$ is locally of finite type by the
chart definition of finite type. Since $\operatorname{Spec}A$ is locally Noetherian,
[pqf-lem-locnoeth-lft] shows that $U$ is locally Noetherian. Thus $Z$ is locally Noetherian in the
chart sense. Its structure module is coherent by [lem-sfb-space-noetherian-coherent-support]. On a
cover trivializing the line module $N$ it is the structure module; hence its chart modules are
locally finite free of rank one and $N$ is coherent.

2. The ideal $\mathfrak m$ has finitely many generators. For each $s\geq1$, their degree-$s$
monomials give a map from a finite direct sum of copies of $N$ to $N$ whose image is exactly
$J^sN$. Finite direct sums, kernels and cokernels of coherent modules are coherent by
[lem-sfb-space-coherent-abelian]; taking the cokernel of the kernel exhibits this image as
coherent. Consequently $J^sN$ and $Q_s=N/J^sN$ are coherent, hence quasi-coherent. Also $\mathfrak
m^s Q_s=0$: the action of every degree-$s$ monomial is zero already as a sheaf map.

3. We may compute additive cohomology and its scalar action by module resolutions. Use
[lem-trf-space-enlarged-etale-ringed-site-model] to work on the equivalent ringed etale site with
terminal object $Z$. An equivalence preserves kernels and cokernels by their universal properties
and preserves injectives by transporting the defining lifting problem along its inverse; therefore
it transports both the global-sections functor and its injective resolutions. Nonnegative
injective module resolutions exist by [lem-sfb-module-resolution-derived-presheaf-comparison]. At
the terminal object [lem-weil-pbc-ringed-site-module-abelian-evaluation-comparison] identifies
their cohomology naturally with additive sheaf cohomology, identically in degree zero. Applying
naturality to multiplication by each $a\in A$ gives the same $A$-action. Global sections with this
action is a left exact additive functor to $A$-modules. Thus
[lem-weil-pbc-right-derived-universal-delta-functor] supplies $A$-linear long exact sequences,
natural in short exact sequences, for the cohomology in the item.

4. Fix $n\geq1$ and set $L_n=H^1(Z,J^nN)$ and $D_n=\Gamma(Z,Q_n)$. The module $L_n$ is finite over
$A$: [lem-sfb-space-proper-coherent-higher-images] makes $R^1g_*(J^nN)$ coherent on
$T=\operatorname{Spec}A$, and [lem-sfb-space-affine-base-higher-image-sections] identifies $L_n$
with its sections on $T$. Properness gives the quasi-compact and quasi-separated hypotheses of the
latter. By the affine-chart characterization of coherence in the former, those sections are
$A\otimes_A M\cong M$ for a finitely generated $A$-module $M$. The cohomology convention agrees by
step 3. Step 2 also gives $\mathfrak m^nD_n=0$, since the scalar sheaf endomorphisms are zero.

5. Apply [lem-sfb-space-ideal-power-cohomology-image-bound] with $I=\mathfrak m$, $F=N$, and
$q=1$. All its hypotheses hold: $A$ is Noetherian, $g$ is proper, and $N$ is coherent by step 1.
Obtain $c\geq0$ such that, for all $m\geq c$, the inclusion-induced map
$a_{n+m,n}:H^1(Z,J^{n+m}N)\to L_n$ has image in $\mathfrak m^{m-c}L_n$. The quotients $Q_s$ are
not the inputs to this estimate; it concerns cohomology of the submodules $J^sN$.

6. For $s\geq1$, the sequence $0\to J^sN\to N\to Q_s\to0$ gives a boundary $\delta_s:D_s\to
H^1(Z,J^sN)$, with $\ker\delta_s=\operatorname{Im}\rho_s$. For $r\geq n$, inclusion on the left,
identity on $N$, and the quotient map $Q_r\to Q_n$ form a morphism of these short exact sequences.
Naturality from [lem-weil-pbc-right-derived-universal-delta-functor] gives
$\delta_n\tau_{r,n}=a_{r,n}\delta_r$. In particular $\delta_n(\operatorname{Im}\tau_{n+m,n})$ lies
in both $\operatorname{Im}\delta_n$ and $\mathfrak m^{m-c}L_n$ for $m\geq c$.

7. Put $B_n=\operatorname{Im}\delta_n\subseteq L_n$. Apply [lem-weil-pbc-artin-rees] to the finite
$A$-module $L_n$, its submodule $B_n$, and the ideal $\mathfrak m$. Obtain $d=d(n)\geq0$ such that
$\mathfrak m^tL_n\cap B_n\subseteq\mathfrak m^{t-d}B_n$ whenever $t\geq d$. Linearity of
$\delta_n$ gives $\mathfrak m^uB_n=\delta_n(\mathfrak m^uD_n)$: both sides consist of finite sums
of $a\delta_n(x)=\delta_n(ax)$. Since $\mathfrak m^nD_n=0$, the intersection is zero as soon as
$t\geq d+n$.

8. Choose $c(n)=c+d(n)+2n\geq n$. For $r\geq c(n)$ write $m=r-n$. Then $m\geq c+d(n)+n$ and
$t=m-c\geq d(n)+n$. Steps 6 and 7 imply $\delta_n\tau_{r,n}=0$, so exactness gives
$\operatorname{Im}\tau_{r,n}\subseteq\ker\delta_n=\operatorname{Im}\rho_n$. This uses a bound on
the source index $r=n+m$; the displayed sufficient bound on $m$ in the source is therefore
converted to a bound on $r$ by adding $n$.

9. The quotient maps satisfy $(N\to Q_r\to Q_n)=(N\to Q_n)$. Taking global sections gives
$\tau_{r,n}\rho_r=\rho_n$. Hence $\operatorname{Im}\rho_n\subseteq\operatorname{Im}\tau_{r,n}$ for
every $r\geq n$. Combining with step 8 proves the equality for all $r\geq c(n)$. None of the steps
uses completeness, flatness, a schematic fibre or ampleness. -/
theorem infinitesimal_section_image_stabilization
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (X : AlgebraicSpace (Spec (CommRingCat.of A)))
    (g : X ⟶ schemeSpace (Over.mk (𝟙 (Spec (CommRingCat.of A)))))
    (hg : MapIsProper g) (N : X.Modules) (hN : X.IsLineModule N) :
    ∀ (n : ℕ), 1 ≤ n → ∃ (c : ℕ) (hnc : n ≤ c),
      ∀ (r : ℕ) (hr : c ≤ r),
        Set.range (SheafOfModules.sectionsMap
          ((baseIdealQuotientTower X (IsLocalRing.maximalIdeal A) N).transition
            r n (hnc.trans hr))) =
        Set.range (SheafOfModules.sectionsMap
          ((baseIdealQuotientTower X (IsLocalRing.maximalIdeal A) N).projection n)) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
