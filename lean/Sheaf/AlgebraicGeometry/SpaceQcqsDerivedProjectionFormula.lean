/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q20
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceDerivedModules
public import Sheaf.AlgebraicGeometry.SpaceAffineHomComparison
public import Sheaf.AlgebraicGeometry.SpaceDerivedTensorPullback
public import Sheaf.AlgebraicGeometry.SpaceDerivedModuleOperations
public import Sheaf.AlgebraicGeometry.ProperCurveModuli
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
import Sheaf.AlgebraicGeometry.SpaceCotangentRingMap
import Sheaf.AlgebraicGeometry.SpaceChartTensorRealization
import Sheaf.Paper.ProjectionMateExact
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
import Sheaf.AlgebraicGeometry.AlgebraicSpaceSmallRingedModel
import Sheaf.AlgebraicGeometry.SpaceQuasiCompactAffineTests
import Sheaf.AlgebraicGeometry.SpaceDerivedEtaleChartCalculus
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.AlgebraicGeometry.AffineEtaleDerivedModuleRealization
import Sheaf.AlgebraicGeometry.SpacePerfectLocalizingGeneration
import Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal
import Mathlib.CategoryTheory.Adjunction.Limits
import Sheaf.AlgebraicGeometry.SpaceDerivedQCohPullbackTensor
import WeilConjectures.Mathlib.CategoryTheory.Triangulated.Functor
import WeilConjectures.CategoryTheory.DerivedModuleFreeGeneration

/-! # The unbounded projection formula for qcqs algebraic-space morphisms

Source: Stacks Project, spaces-perfect.tex, Tag 08IN, lemma-cohomology-base-change
(blueprint: lem-sfb-space-qcqs-derived-projection-formula).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- The canonical counit-mate projection morphism is invertible for quasi-coherent inputs.
Source: Stacks Project, spaces-perfect.tex, Tag 08IN, lemma-cohomology-base-change
(blueprint: lem-sfb-space-qcqs-derived-projection-formula).

Proof:
1. Uses lem-trf-space-enlarged-etale-ringed-site-model,
lem-trf-space-chart-adjunction-tensor-realization,
lem-weil-pbc-ringed-projection-mate-exact.
The enlarged ringed model and chart tensor realization identify the ordinary
adjunction with its normalized ringed-topos model. The projection-mate exactness theorem
makes the displayed mate a natural transformation of exact, shift-compatible functors.
At the structure sheaf it is the identity under the normalized unit comparisons.
2. Uses lem-trf-space-fibre-products-etale-covers,
def-sfb-space-small-ringed-model,
lem-sfb-space-quasicompact-affine-tests,
lem-sfb-space-derived-etale-chart-calculus,
lem-weil-pbc-ringed-topoi-derived-tensor-pullback,
lem-sfb-space-etale-conservative-geometric-points.
Choose an affine etale cover of the target and base change the morphism.
Quasi-compact affine tests and fibre-product calculus preserve qcqs. Derived etale chart
calculus identifies restriction of both sides and of the mate with the base-changed
ones, respecting the counit. Tensor pullback gives its tensor comparison. Geometric
stalk conservativity detects isomorphisms of cohomology, so it suffices to work over an
affine scheme. The restrictions of both inputs retain quasi-coherent cohomology.
3. Uses lem-sfb-affine-etale-derived-module-realization,
lem-sfb-space-perfect-localizing-generation.
Affine etale derived-module realization identifies the target's quasi-coherent
subcategory with D(A), taking A[k] to the shifted structure sheaf. Perfect localizing
generation gives closure under the ambient coproducts and distinguished triangles.
4. Uses lem-weil-pbc-ringed-projection-mate-exact,
lem-sf-ringed-derived-closed-symmetric-monoidal,
lem-weil-pbc-left-adjoint-preserves-colimits,
lem-sfb-space-derived-qcoh-pullback-tensor,
lem-sfb-space-derived-pushforward-coproducts.
Tensor and pullback preserve coproducts as left adjoints. Derived pullback and
tensor preserve quasi-coherent cohomology; qcqs derived direct image preserves their
coproducts. Naturality for the coprojections identifies the mate on a coproduct with
the coproduct of its components, hence preserves the isomorphism locus.
5. Uses lem-weil-pbc-ringed-projection-mate-exact,
lem-sf-triangle-two-out-of-three.
Projection-mate exactness and triangle two-out-of-three make that locus closed
under triangles and all integer shifts. The unit normalization gives every O[k].
6. Naturality gives closure under isomorphisms and retracts. If i:L to M and p:M to L
satisfy i followed by p equals the identity, the inverse at L is B(i), followed by
the inverse at M, followed by A(p). Both inverse identities follow from naturality.
7. Uses lem-sfb-affine-etale-derived-module-realization,
lem-pc-derived-module-free-generation.
Transport this locus to D(A). The affine equivalence preserves coproducts,
shifts, triangles and retracts. Derived-module free generation by A[k] makes the
locus all of D(A). Essential surjectivity proves the affine case; step 2 gives the
general case. Every map throughout is the displayed canonical adjunction mate. -/
theorem isIso_qcqs_derived_projection_mate
    {S : Scheme.{u}} {Y Z : AlgebraicSpace S}
    [HasDerivedCategory.{w} Y.SmallModules] [HasDerivedCategory.{w} Z.SmallModules]
    (g : Y ⟶ Z)
    (hqc : MapIsQuasiCompact g.hom.hom)
    (hqs : MapIsQuasiCompact (pullback.diagonal g.hom.hom))
    (F : Y.DerivedModules) (L : Z.DerivedModules)
    (hF : Y.derivedQCohProperty F) (hL : Z.derivedQCohProperty L) :
    IsIso ((spaceDerivedAdjunction g).homEquiv _ _
      ((moduleDerivedPullbackTensor g).hom.app ((derivedDirectImage g).obj F, L) ≫
        Y.derivedDualityModel.closed.tensor.map
          (Prod.mkHom ((spaceDerivedAdjunction g).counit.app F)
            (𝟙 ((derivedTensorPullback g).obj L))))) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
