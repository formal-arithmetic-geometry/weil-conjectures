/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q129
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.AlgebraicGeometry.Scheme
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceSmallRingedModel
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceDerivedModules
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceAbsoluteQuasiSeparated
public import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Homology.FunctorialBoundedAboveClassResolution
import Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat
import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentPushforward
import Sheaf.AlgebraicGeometry.SpaceDerivedEtaleChartCalculus
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.AlgebraicGeometry.SpaceEtalePullPushRetract
import Sheaf.AlgebraicGeometry.DerivedEtaleZariskiEquivalence
import WeilConjectures.AlgebraicGeometry.TorAmplitudeQCohTest
import Mathlib.AlgebraicGeometry.AffineScheme

/-! # Quasi-coherent tests for Tor amplitude on algebraic spaces

Source: Stacks Project, spaces-perfect.tex, Tags 08IL and 08IS
(blueprint: lem-sfb-space-quasicoherent-tor-amplitude-test).

The existing small affine ringed model represents the small étale module topos,
with its original section universe. Tensor is the recorded K-flat derived tensor.
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- For a bounded-above object with quasi-coherent cohomology on a quasi-separated
algebraic space, quasi-coherent module tests detect the lower Tor bound.

Source: Stacks Project, spaces-perfect.tex, Tag 08IL (lemma-tor-qc-qs), and
Tag 08IS (lemma-perfect-direct-image), its upper derived-tensor bound
(blueprint: lem-sfb-space-quasicoherent-tor-amplitude-test).

Proof:
1. Good truncation at c represents K by a complex zero above c. Resolve it by
   flat terms without increasing c, using lem-trf-site-functorial-flat-resolution
   and lem-sfb-functorial-bounded-above-class-resolution. The resulting bounded-above
   flat complex is K-flat by lem-pc-bounded-above-flat-kflat-site. Its tensor with
   any module in degree zero is zero above c, giving the upper bound for all modules.
2. The full Tor interval implies the lower bound for quasi-coherent tests immediately.
   Conversely the assumed lower bound and step 1 give the full interval for these tests.
3. For an affine étale chart j : U → Y, quasi-separatedness makes j quasi-compact
   and separated (lem-sfb-space-affine-source-qc-separated). Thus j_* sends
   quasi-coherent modules to quasi-coherent modules by
   lem-trf-space-qc-separated-quasi-coherent-pushforward. Apply step 2 to j_*G.
4. Exact étale restriction and tensor pullback identify the restricted tensor with
   j^*K tensor j^*j_*G, by lem-sfb-space-derived-etale-chart-calculus and
   lem-weil-pbc-ringed-topoi-derived-tensor-pullback. The counit splits by
   lem-sfb-space-etale-pull-push-retract. Tensor and cohomology preserve the retract,
   proving the full interval test for quasi-coherent G on U. Restriction preserves
   quasi-coherent cohomology by the chart calculus.
5. Use lem-sfb-derived-etale-zariski-equivalence to write j^*K as epsilon^*K_0.
   Tensor pullback and the exact, faithful epsilon^* transfer the quasi-coherent
   tests to the Zariski site of U.
6. The affine scheme U is quasi-separated (lem-weil-pbc-affine-scheme-qcqs).
   Apply lem-pc-tor-amplitude-qcoh-test with a ≤ c. Then
   lem-sfb-etale-tor-dimension-descent transfers this full Tor interval to U_et.
7. For an arbitrary module on Y, exact étale restriction and tensor comparison now
   give zero cohomology outside [a,c] on every affine étale chart. Every chart has
   an affine open covering (lem-weil-pbc-affine-opens-basis). Sheaf uniqueness
   (def-weil-sheaf-of-modules-category) gives global vanishing.

The specified module restriction equivalence transports all module tests and
cohomology; quasi-coherence is evaluated after its inverse. Thus quantification on
SmallModules is quantification on all original étale module sheaves. -/
theorem torAmplitude_iff_quasiCoherent_lower_tests
    {S : Scheme.{u}} (Y : AlgebraicSpace S)
    [HasDerivedCategory.{w} Y.SmallModules]
    (hY : IsAbsolutelyQuasiSeparated Y)
    (K : Y.DerivedModules) (hK : Y.derivedQCohProperty K)
    (c : ℤ)
    (hupper : ∀ i : ℤ, c < i →
      IsZero ((DerivedCategory.homologyFunctor Y.SmallModules i).obj K))
    (a : ℤ) (hac : a ≤ c) :
    (∀ (G : Y.SmallModules) (i : ℤ), i < a ∨ c < i →
      IsZero ((DerivedCategory.homologyFunctor Y.SmallModules i).obj
        ((SheafOfModules.siteDerivedTensorIndependentCoefficients.{u, u, u, w}
          Y.smallEtaleModelTopology Y.smallStructureSheaf).obj
            (K, (DerivedCategory.singleFunctor Y.SmallModules 0).obj G)))) ↔
    (∀ (F : Y.SmallModules),
      ((Y.smallModuleEquivalence.inverse).obj F).IsQuasicoherent →
      ∀ i : ℤ, i < a →
        IsZero ((DerivedCategory.homologyFunctor Y.SmallModules i).obj
          ((SheafOfModules.siteDerivedTensorIndependentCoefficients.{u, u, u, w}
            Y.smallEtaleModelTopology Y.smallStructureSheaf).obj
              (K, (DerivedCategory.singleFunctor Y.SmallModules 0).obj F)))) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
