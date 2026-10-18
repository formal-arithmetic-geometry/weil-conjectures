/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N9
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleDirectImageComparison
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModules
public import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction

import Sheaf.RingTheory.IndEtaleUniverseTransport
import WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Sheaf.AlgebraicGeometry.ModuleCohomologyConventions
import Sheaf.AlgebraicGeometry.ProEtaleClassicalBounds
import Sheaf.SixFunctors.UnboundedClassicalTruncation
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import Sheaf.Algebra.Homology.KInjectiveRestrictLocalized
import WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian
import Sheaf.CategoryTheory.DerivedCategory.FiniteCDDerivedUpperBound
import Sheaf.AlgebraicGeometry.EtaleConstantModuleDirectImageLeftExact
import Sheaf.AlgebraicGeometry.EtaleModuleEnoughInjectives
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import Sheaf.CategoryTheory.ModuleAbelianEvaluationComparison
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import Sheaf.AlgebraicGeometry.ProEtaleClassicalSheaves

import Sheaf.AlgebraicGeometry.ClassicalContinuityMap
import Sheaf.AlgebraicGeometry.ClassicalDerivedDefinitions
import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
import Sheaf.CategoryTheory.Sites.UnboundedSectionsLocalization
/-!
# Unbounded direct-image comparison

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/
sk-prop-pe-unbounded-classical/sk-prop-pe-unbounded-classical-direct-image.md
(blueprint: lem-sfb-unbounded-direct-image-comparison).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

/-- Apply the exact inverse images termwise and localize the specified comparison square.
Source: blueprint, sk-prop-pe-unbounded-classical-direct-image.md; the inverse-image
comparison is sk-thm-pe-direct-image-comparison
(blueprint: lem-sfb-unbounded-direct-image-comparison). -/
noncomputable def unboundedDirectImagePullbackIso
    (A : Type (u + 1)) [CommRing A] {X Y : Scheme.{u}} (g : X ⟶ Y) :
    (comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory ⋙
        (ProEtale.upperStar (ModuleCat.{u + 1} A) g).mapDerivedCategory ≅
      (Etale.upperStar (ModuleCat.{u + 1} A) g).mapDerivedCategory ⋙
        (comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso
    (comparisonUpperStar (ModuleCat.{u + 1} A) Y)
    (ProEtale.upperStar (ModuleCat.{u + 1} A) g)).symm ≪≫
    Functor.mapDerivedCategoryNatIso
      (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} A) g) ≪≫
    Functor.mapDerivedCategoryCompIso
      (Etale.upperStar (ModuleCat.{u + 1} A) g)
      (comparisonUpperStar (ModuleCat.{u + 1} A) X)

/-- The specified unbounded comparison: transpose the pullback-square identification
followed by the etale derived counit under the pro-etale derived adjunction.
All direct images are total right derived functors on K-injective resolutions.
Source: blueprint, sk-prop-pe-unbounded-classical-direct-image.md, displayed mate
(blueprint: lem-sfb-unbounded-direct-image-comparison). -/
noncomputable def unboundedDirectImageComparisonMap
    (A : Type (u + 1)) [CommRing A] {X Y : Scheme.{u}} (g : X ⟶ Y)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.obj
        ((Etale.lowerStar (ModuleCat.{u + 1} A) g).rightDerivedFunctor.obj K) ⟶
      (ProEtale.lowerStar (ModuleCat.{u + 1} A) g).rightDerivedFunctor.obj
        ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj K) :=
  ((ProEtale.upperStarLowerStarAdjunction
    (ModuleCat.{u + 1} A) g).mapDerivedCategoryRightDerivedAdjunction.homEquiv _ _)
    ((unboundedDirectImagePullbackIso A g).hom.app
        ((Etale.lowerStar (ModuleCat.{u + 1} A) g).rightDerivedFunctor.obj K) ≫
      (comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.map
        ((Etale.upperStarLowerStarAdjunction
          (ModuleCat.{u + 1} A) g).mapDerivedCategoryRightDerivedAdjunction.counit.app K))

/-- The canonical comparison is invertible on every unbounded etale complex over a finite
primary ring. Fixed-ring module sheaves are the ordinary constant-ring module sheaves;
the finiteCoefficientRealization of def-weil-pbc-proetale-modules identifies their
pro-etale realization with the continuous-function coefficient presentation.
Source: blueprint, sk-prop-pe-unbounded-classical-direct-image.md and its proof
(blueprint: lem-sfb-unbounded-direct-image-comparison).

Proof:
1. Empty source or target gives zero. Otherwise use the affine ind-etale basis over
   affine opens of Y (def-weil-pbc-ind-etale-basis, lem-weil-pbc-ind-etale-basis).
2. Fix a basis object V and degree m. Put eX = 2 dim X + 1, eY = 2 dim Y + 1,
   and choose N < m - eX - eY - 1. Truncate K by E = tau_{<N} K. Ringed-site modules
   are Grothendieck and have enough injectives, so K-injective resolutions compute
   the total derived functors (sk-def-sfb-derived-categories). Derived direct images,
   sections and exact inverse images preserve the truncation triangle.
3. Since ell^r kills A, all coefficient modules are torsion. The etale higher-direct-image
   bound of det-pe-unbounded-classical-bounds transfers through the module/abelian
   comparison det-pbc-conventions-module-cohomology, giving bound eX.
4. lem-sf-finite-cd-derived-upper-bound bounds Rg_et,* E above N-1+eX.
   Exact comparison preserves this bound and makes its cohomology classical.
5. Classical sheaves on V have evaluation bound eY by det-pe-unbounded-classical-bounds.
   Use weakly-etale localization and the ringed-site module/abelian evaluation comparison;
   lem-sfb-unbounded-sections-localization identifies localized and ordinary sections.
6. det-pe-unbounded-classical-truncation kills the source-tail sections in degrees m,m+1.
7. Direct image preserves K-injectives, since its left adjoint is exact
   (lem-weil-pbc-right-adjoint-preserves-kinjective). Evaluate a resolution to identify
   RΓ(V,Rg_* M) with RΓ(X times_Y V,M), using the same localization lemma.
8. The classical cohomology of nu_X^* E vanishes above N-1. The bound on X times_Y V
   in det-pe-unbounded-classical-bounds and the truncation lemma kill the target tail
   in degrees m,m+1; no affineness of that fiber product is required.
9. Finite type makes g quasi-compact; local noetherianity makes it quasi-separated
   (pqf-lem-locnoeth-lft, lem-weil-pbc-locally-noetherian-quasi-separated).
   sk-thm-pe-direct-image-comparison makes the specified mate invertible on tau_{>=N} K.
10. The two long exact cohomology sequences have zero end terms. Naturality of the mate
    and the bounded-below result imply invertibility on every H^m RΓ(V,-).
11. Represent the mate between K-injectives by a chain map using
    lem-weil-pbc-kinjective-hom-derived. Exact module sheafification identifies the
    sheafification of sectionwise cohomology with the cohomology sheaf (Stacks 0BKV).
12. Basis objects cover every object, so the kernel and cokernel presheaves of the map
    on sectionwise cohomology have zero sheafifications. Thus the map on every cohomology
    sheaf is invertible. lem-weil-pbc-unbounded-derived-iso-cohomology concludes.
-/
theorem unboundedDirectImageComparison
    (k : Type u) [Field k] (hbase : Finite k ∨ IsAlgClosed k)
    {ℓ : ℕ} [Fact ℓ.Prime]
    (hℓ : IsUnit (algebraMap ℤ k (ℓ : ℤ)))
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (hA : ∃ n : ℕ, (ℓ : A) ^ n = 0)
    {X Y : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k))] [Y.Over (Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of k))]
    (g : X ⟶ Y)
    [LocallyOfFiniteType g] [QuasiCompact g]
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    IsIso (unboundedDirectImageComparisonMap A g K) := by
  sorry

end AlgebraicGeometry.ProEtale
