/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ScalarDirectImageMateCoherence
public import WeilConjectures.SixFunctors.ScalarSixTensorComparison
public import WeilConjectures.AlgebraicGeometry.ModuleObjectProjectionMap
public import WeilConjectures.AlgebraicGeometry.CondensedSupportProjectionFormula
public import WeilConjectures.CategoryTheory.InternalSectionTensorComparison
public import WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Monoidal.Internal.FunctorCategory
public import WeilConjectures.CategoryTheory.RingObjects.Ab
public import WeilConjectures.CategoryTheory.Sites.MonObj
public import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
public import WeilConjectures.CategoryTheory.SheafTensor
public import WeilConjectures.CategoryTheory.SheafTensorStructure
public import Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import WeilConjectures.CategoryTheory.PresheafTensorInternalHom
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Preadditive
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import WeilConjectures.CategoryTheory.SheafificationTensorLocalIso
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Monoidal.Braided.Reflection
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctorialitySupplement
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.ModuleObjects.Symmetric
public import WeilConjectures.CategoryTheory.ModuleObjects.Abelian
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
public import WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap
public import WeilConjectures.CategoryTheory.InternalSectionModuleFlat
public import WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import WeilConjectures.CategoryTheory.InternalSectionScalarAdjunctionSupplement
public import WeilConjectures.AlgebraicGeometry.RingedTopoiCanonicalTensorPullbackOfUniverses

import WeilConjectures.AlgebraicGeometry.InternalScalarPullbackNormalization
import WeilConjectures.AlgebraicGeometry.KFlatScalarComparisonNormalization
import WeilConjectures.SixFunctors.RingedDerivedMonoidalComparisons
import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapMate
import WeilConjectures.AlgebraicGeometry.ProEtaleRingedOpenComparison
import WeilConjectures.Algebra.Homology.RingedOpenTotalTensorKFlat
import WeilConjectures.Algebra.Homology.KFlatTotalTensorModelSupplement
import WeilConjectures.CategoryTheory.RingedSliceExtensionTensor
import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.CategoryTheory.RingedSliceExtensionTensorHomData
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses

/-! # Scalar compatibility of the condensed proper and open projection factors

Source: latest blueprint, sec-six-functors/sk-rem-sf-pf-done,
fix-prop-projection-formula.proof.md, scalar-extension sentence; scalar-six-pullback,
clauses (1)--(2); Stacks Tags 07A4, 0D6D and 0E8I.
(blueprint: lem-sf-condensed-projection-factor-scalar-identities).

Exact inverse image is written using its termwise localization, as in the recorded
scalar comparison and direct-image mate. The projection arrows are transported along
only the published comparison from total left derivation to this exact presentation.
All tensors are Layer B relative derived tensors. No flatness of scalar change is used.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The factor a^f: first the canonical scalar tensor comparison, then inverse c_f
in the second tensor factor. Here c_f is inverse theta of the recorded pullback data.
The scalar tensorator is the K-flat derived ordinary balanced tensorator, sending
s tensor (x tensor y) to (s tensor x) tensor (1 tensor y) on each signed total summand.
Source: latest blueprint scalar-extension sentence and scalar-six-pullback (1);
Stacks 07A4 (blueprint: lem-sf-condensed-projection-factor-scalar-identities). -/
def condensedProjectionScalarFactor {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ')
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (V : DerivedCategory (ModuleRingedComparison.internalModules Λ.X X))
    (W : DerivedCategory (ModuleRingedComparison.internalModules Λ.X Y)) :
    (scalarSixChange a X).obj (V ⊗ (scalarSixPull Λ f).obj W) ⟶
      (scalarSixChange a X).obj V ⊗ (scalarSixPull Λ' f).obj ((scalarSixChange a Y).obj W) :=
  (scalarSixTensorIso a X V ((scalarSixPull Λ f).obj W)).hom ≫
    (scalarSixChange a X).obj V ◁ (scalarDirectImagePullbackData.theta a f).hom.app W

/-- The specified projection map in the exact-pullback presentation. The only
postcomposition is Rf_* of identity tensor the published Lf^* to D(f^*) comparison.
Source: latest blueprint projection map; Stacks 07A4 and 0D6D
(blueprint: lem-sf-condensed-projection-factor-scalar-identities). -/
def condensedProjectionExactFactor (Λ : ScalarSixRing.{u})
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : DerivedCategory (ModuleRingedComparison.internalModules Λ.X X))
    (N : DerivedCategory (ModuleRingedComparison.internalModules Λ.X Y)) :
    (RootCoordinateFace.lower Λ.X f).obj M ⊗ N ⟶
      (RootCoordinateFace.lower Λ.X f).obj (M ⊗ (scalarSixPull Λ f).obj N) :=
  moduleObjectProjectionMap Λ.X f M N ≫
    (RootCoordinateFace.lower Λ.X f).map
      (M ◁ (leftDerivedUpperStarIsoMapDerivedCategory Λ.X f).hom.app N)

/-- The inverse of the canonical open support projection, transported from support
inverse image to the recorded exact inverse image. Invertibility is supplied by the
recorded support theorem applied to the canonical closed complement of j.
Source: latest blueprint scalar-six-pullback (2); Stacks 0E8I
(blueprint: lem-sf-condensed-projection-factor-scalar-identities). -/
def condensedProjectionOpenFactor (Λ : ScalarSixRing.{u})
    {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] [QuasiCompact j]
    (K : DerivedCategory (ModuleRingedComparison.internalModules Λ.X X))
    (N : DerivedCategory (ModuleRingedComparison.internalModules Λ.X Z)) :
    (openImmersionLowerShriek Λ.X j).mapDerivedCategory.obj K ⊗ N ⟶
      (openImmersionLowerShriek Λ.X j).mapDerivedCategory.obj
        (K ⊗ (scalarSixPull Λ j).obj N) :=
  @CategoryTheory.inv _ _ _ _ (openSupportProjection Λ.X j K N)
      ((openClosedSupportProjectionFormula Λ.X j.closedComplement j
        j.range_closedComplement).2 K N) ≫
    (openImmersionLowerShriek Λ.X j).mapDerivedCategory.map
      (K ◁ (Functor.mapDerivedCategoryNatIso
        (supportPullbackIsoUpperStar Λ.X j)).hom.app N)

/-- Arbitrary condensed coefficient change respects the specified direct-image and open
projection factors, as equalities of morphisms in the ordinary unbounded derived categories.
The direct-image arrow is the recorded mate of inverse theta; the open scalar arrow is
`derivedOpenImmersionShriekIso`, computed termwise on flat-term K-flat representatives.
No invertibility of a direct-image mate or of a direct-image projection is asserted.

Source: latest blueprint fix-prop-projection-formula.proof.md, scalar-extension sentence,
and det-prop-scalar-six-pullback.proof.md (1)--(2); Stacks 07A4, 0D6D and 0E8I
(blueprint: lem-sf-condensed-projection-factor-scalar-identities).

Proof:
1. Use the internal/section tensor equivalence and scalar-adjunction comparison to
identify scalar change with identity-topos ringed pullback. Its canonical tensorator
is the signed total of the balanced formula in condensedProjectionScalarFactor.
The internal scalar/pullback and K-flat scalar normalizations identify inverse theta
with the two ringed pullback-composition comparisons, preserving units and counits.
2. Ringed derived monoidal comparisons applied to the coefficient square show that
these scalar tensorators commute with the geometric pullback tensorators. This uses
no exactness of underived scalar extension and is not a geometric base-change assertion.
3. Apply the categorical projection-mate square to the specified derived adjunctions,
these tensorators and inverse theta. The projection-map definition and scalar mate
coherence identify its arrows with the first equation below. Transport through the
published exact-pullback comparison gives precisely condensedProjectionExactFactor.
4. The pro-etale ringed-open comparison identifies open pullback with site restriction.
The exact open extension adjunction and internal/section tensor equivalence identify
the ordinary open tensor map with the canonical support projection. The signed total
comparison of ringedOpen_totalTensor_kFlat therefore gives its inverse g.
5. Choose flat-term K-flat representatives for K,N'. Ringed pullback preserves them;
the total-tensor model gives K-flatness of their tensor, and open extension preserves
K-flatness. Its terms are flat by the ordinary ringed-slice extension/tensor formula.
Consequently all complexes used by scalar change and both tensors compute the derived
objects, even for a nonflat coefficient map.
6. Both open composites send s tensor ([x] tensor y) to the open summand of
(s restricted to X tensor x) tensor (1 tensor j^*y). Balanced coprojections determine
these maps without an enough-points argument. No homogeneous factors are interchanged,
so their signed total differentials agree. Localization proves the second equation;
the internal/section equivalence reflects equality. -/
theorem condensedProjectionFactorScalarIdentities
    {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ')
    {X Z Y : Scheme.{u}} (p : Z ⟶ Y) (j : X ⟶ Z)
    [IsOpenImmersion j] [QuasiCompact j]
    (M : DerivedCategory (ModuleRingedComparison.internalModules Λ.X Z))
    (K : DerivedCategory (ModuleRingedComparison.internalModules Λ.X X))
    (N : DerivedCategory (ModuleRingedComparison.internalModules Λ.X Y))
    (N' : DerivedCategory (ModuleRingedComparison.internalModules Λ.X Z)) :
    ((scalarSixChange a Y).map (condensedProjectionExactFactor Λ p M N) ≫
        (scalarDirectImageMate a p).app (M ⊗ (scalarSixPull Λ p).obj N) ≫
        (RootCoordinateFace.lower Λ'.X p).map (condensedProjectionScalarFactor a p M N) =
      (scalarSixTensorIso a Y ((RootCoordinateFace.lower Λ.X p).obj M) N).hom ≫
        ((scalarDirectImageMate a p).app M ▷ (scalarSixChange a Y).obj N) ≫
        condensedProjectionExactFactor Λ' p ((scalarSixChange a Z).obj M)
          ((scalarSixChange a Y).obj N)) ∧
    ((scalarSixChange a Z).map (condensedProjectionOpenFactor Λ j K N') ≫
        (derivedOpenImmersionShriekIso (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom j).hom.app
          (K ⊗ (scalarSixPull Λ j).obj N') ≫
        (openImmersionLowerShriek Λ'.X j).mapDerivedCategory.map
          (condensedProjectionScalarFactor a j K N') =
      (scalarSixTensorIso a Z
        ((openImmersionLowerShriek Λ.X j).mapDerivedCategory.obj K) N').hom ≫
        ((derivedOpenImmersionShriekIso (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom j).hom.app K ▷
          (scalarSixChange a Z).obj N') ≫
        condensedProjectionOpenFactor Λ' j ((scalarSixChange a X).obj K)
          ((scalarSixChange a Z).obj N')) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
