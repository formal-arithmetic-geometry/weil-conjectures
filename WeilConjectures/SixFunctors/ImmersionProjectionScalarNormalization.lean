/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ListedCoefficientMaps
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import WeilConjectures.AlgebraicGeometry.LocallyClosedExtensionCoherence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.SixFunctors.ScalarSixDirectImage
public import WeilConjectures.SixFunctors.ScalarSixCompactSupport
public import WeilConjectures.SixFunctors.ScalarCompositeModelPasting
public import WeilConjectures.SixFunctors.RingedDerivedMonoidalComparisons
public import WeilConjectures.AlgebraicGeometry.CondensedOpenClosedInternalHomMaps
public import WeilConjectures.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctorialitySupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import WeilConjectures.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
public import WeilConjectures.Algebra.Homology.SheafRingDerivedHomComparison
public import WeilConjectures.CategoryTheory.DerivedCategory.ResolvingClassEssentialConstancy
public import WeilConjectures.CategoryTheory.DerivedCategory.DerivedAdjunctionCompatibility
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantInd
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Limits.Cones
public import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantPro
public import Mathlib.Algebra.Homology.DerivedCategory.Fractions
public import Mathlib.CategoryTheory.Functor.Derived.Adjunction
public import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedPointwiseKanBridge
public import WeilConjectures.Algebra.Homology.QuasiIsoSaturatedTriangulated
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
public import WeilConjectures.AlgebraicGeometry.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MonoidalStructure
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsFlat

import WeilConjectures.AlgebraicGeometry.CondensedSupportDerivedLocalization
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Normalized immersion projection and scalar comparison

Source: literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-lem-int-tensor/
det-lem-int-tensor-projection.proof.md, Open immersions, Closed immersions, Derived version
and Locally closed immersions; Stacks Tags 0E8I, 0B56, 0E48, 09BM and 09BN.
(blueprint: lem-sfb-immersion-projection-scalar-normalization).

All tensors are relative, ordinary and uncompleted, and all derived categories are
unbounded. The specified maps are actual adjunction transposes. The separately derived
compactification model is identified with the exact immersion model by the canonical
exact-functor comparison; scalar extension is never assumed flat.

## Main definitions and statements

* `immersionClosedProjection`, `immersionOpenProjection`: the specified adjunction maps.
* `immersionProjection`: their composite with the two symmetries and pullback compositor.
* `immersionOpenScalarMap`, `immersionScalarMap`: the normalized coefficient comparisons.
* `ImmersionClosedScalarSquare`, `ImmersionOpenScalarSquare`,
  `ImmersionProjectionScalarSquare`: the actual commutation equations.
* `immersionProjectionScalarNormalization`: invertibility and scalar compatibility.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- Transport the existing normalized support tensor comparison to the recorded upper star.
Source: Stacks 0G7D and the derived paragraph of the source
(blueprint: lem-sfb-immersion-projection-scalar-normalization). -/
def immersionPullTensor (Λ : ScalarSixRing.{u}) {S X : Scheme.{u}} (f : S ⟶ X)
    (C D : DerivedCategory (supportModules Λ.X X)) :
    (scalarSixPull Λ f).obj (C ⊗ D) ≅
      (scalarSixPull Λ f).obj C ⊗ (scalarSixPull Λ f).obj D :=
  (Functor.mapDerivedCategoryNatIso (supportPullbackIsoUpperStar Λ.X f)).symm.app (C ⊗ D) ≪≫
    supportDerivedTensorComparison Λ.X f C D ≪≫
      tensorIso
        ((Functor.mapDerivedCategoryNatIso (supportPullbackIsoUpperStar Λ.X f)).app C)
        ((Functor.mapDerivedCategoryNatIso (supportPullbackIsoUpperStar Λ.X f)).app D)

/-- The specified closed projection is the geometric adjunction transpose of the tensor
comparison followed by counit tensor identity. Direct image is written in its total
right-derived presentation until the exact-functor identification below.
Source: Stacks 0B56, closed-immersion paragraph of the source
(blueprint: lem-sfb-immersion-projection-scalar-normalization). -/
def immersionClosedProjection (Λ : ScalarSixRing.{u}) {Z X : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i]
    (B : DerivedCategory (supportModules Λ.X Z))
    (C : DerivedCategory (supportModules Λ.X X)) :
    (RootCoordinateFace.lower Λ.X i).obj B ⊗ C ⟶
      (RootCoordinateFace.lower Λ.X i).obj (B ⊗ (scalarSixPull Λ i).obj C) :=
  (RootCoordinateFace.adjunction Λ.X i).homEquiv _ _
    ((immersionPullTensor Λ i ((RootCoordinateFace.lower Λ.X i).obj B) C).hom ≫
      ((RootCoordinateFace.adjunction Λ.X i).counit.app B ⊗ₘ 𝟙 _))

/-- The specified open tensor map, in ambient-first tensor order, is the open adjunct of
identity tensor the open unit followed by the inverse pullback tensor comparison.
Source: Stacks 0E8I, open-immersion and derived paragraphs of the source
(blueprint: lem-sfb-immersion-projection-scalar-normalization). -/
def immersionOpenProjection (Λ : ScalarSixRing.{u}) {S Z : Scheme.{u}}
    (j : S ⟶ Z) [IsOpenImmersion j]
    (L : DerivedCategory (supportModules Λ.X S))
    (D : DerivedCategory (supportModules Λ.X Z)) :
    (openImmersionLowerShriek Λ.X j).mapDerivedCategory.obj
        ((scalarSixPull Λ j).obj D ⊗ L) ⟶
      D ⊗ (openImmersionLowerShriek Λ.X j).mapDerivedCategory.obj L :=
  ((derivedOpenImmersionLowerShriekUpperStarAdjunction Λ.X j).homEquiv _ _).symm
    ((𝟙 _ ⊗ₘ (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ.X j).unit.app L) ≫
      (immersionPullTensor Λ j D
        ((openImmersionLowerShriek Λ.X j).mapDerivedCategory.obj L)).inv)

/-- The specified open tensor map is invertible on all unbounded inputs.
Source: Stacks 0E8I and 09BN, open and derived paragraphs
(blueprint: lem-sfb-immersion-projection-scalar-normalization).

Proof: the standing target is Noetherian by finite type over the field, so the open is
quasi-compact and has a complementary closed immersion. Apply
lem-sfb-condensed-support-projection-formula to the published openSupportProjection.
Conjugate by the two Koszul symmetries and supportPullbackIsoUpperStar. The open
Hom bijection identifies the conjugate with the displayed unit adjunct, hence with
immersionOpenProjection. On flat-term K-flat models this is the sheaf map of Tag 0E8I;
exact localization preserves its adjunct by lem-sf-exact-localization-inverse-mate. -/
theorem immersionOpenProjection_isIso (Λ : ScalarSixRing.{u}) (k : Type u) [Field k]
    {S Z : Over (Spec (.of k))}
    [LocallyOfFiniteType S.hom] [QuasiCompact S.hom] [IsSeparated S.hom]
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
    (j : S ⟶ Z) [IsOpenImmersion j.left]
    (L : DerivedCategory (supportModules Λ.X S.left))
    (D : DerivedCategory (supportModules Λ.X Z.left)) :
    IsIso (immersionOpenProjection Λ j.left L D) := by
  let W : TopologicalSpace.Closeds Z.left :=
    ⟨(Set.range j.left.base)ᶜ, j.left.isOpenEmbedding.isOpen_range.isClosed_compl⟩
  let J := Scheme.IdealSheafData.vanishingIdeal W
  let i := J.subschemeι
  have hij : Set.range i.base = (Set.range j.left.base)ᶜ := by
    change Set.range J.subschemeι = _
    rw [J.range_subschemeι]
    simp [J, W]
  have : IsLocallyNoetherian Z.left :=
    LocallyOfFiniteType.isLocallyNoetherian Z.hom
  have : CompactSpace Z.left := QuasiCompact.compactSpace_of_compactSpace Z.hom
  have : IsNoetherian Z.left := ⟨⟩
  have : QuasiCompact j.left := inferInstance
  let := closedSupport_lowerStarExact Λ.X i j.left hij
  obtain ⟨_, _, _, hio, _, hd⟩ :=
    condensedSupportDerivedLocalization Λ.X i j.left hij
  apply hd
  · have hsrc := hio ((scalarSixPull Λ j.left).obj D ⊗ L)
    have htgt : IsZero ((supportPullback Λ.X i).mapDerivedCategory.obj
        (D ⊗ (openImmersionLowerShriek Λ.X j.left).mapDerivedCategory.obj L)) := by
      exact ((tensorLeft ((supportPullback Λ.X i).mapDerivedCategory.obj D)).map_isZero
        (hio L)).of_iso (supportDerivedTensorComparison Λ.X i D
          ((openImmersionLowerShriek Λ.X j.left).mapDerivedCategory.obj L))
    exact isIso_of_source_target_iso_zero _ hsrc.isoZero htgt.isoZero
  · apply (NatIso.isIso_map_iff
      (Functor.mapDerivedCategoryNatIso (supportPullbackIsoUpperStar Λ.X j.left)) _).2
    let adj := derivedOpenImmersionLowerShriekUpperStarAdjunction Λ.X j.left
    have : IsIso adj.unit := Adjunction.isIso_mapDerivedCategoryAdjunction_unit _
    have hh : IsIso (adj.homEquiv _ _ (immersionOpenProjection Λ j.left L D)) := by
      dsimp only [adj, immersionOpenProjection]
      simp only [Equiv.apply_symm_apply]
      infer_instance
    have hcomp : IsIso (adj.unit.app ((scalarSixPull Λ j.left).obj D ⊗ L) ≫
        (upperStar Λ.X j.left).mapDerivedCategory.map
          (immersionOpenProjection Λ j.left L D)) := by
      erw [← adj.homEquiv_unit _ _ (immersionOpenProjection Λ j.left L D)]
      exact hh
    have hi := IsIso.of_isIso_comp_left
      (adj.unit.app ((scalarSixPull Λ j.left).obj D ⊗ L))
      ((upperStar Λ.X j.left).mapDerivedCategory.map (immersionOpenProjection Λ j.left L D))
    exact hi

/-- Closed direct image is exact in the standing setting.
Source: Stacks 09BM; closed and derived paragraphs
(blueprint: lem-sfb-immersion-projection-scalar-normalization).

Proof: X is Noetherian by lem-weil-pbc-finite-type-over-noetherian, and its open
complement is quasi-compact by lem-sfb-noetherian-space-compact-subsets. The image
and its complement form the support pair. Apply closedSupport_lowerStarExact from
lem-sfb-condensed-support-derived-localization. Left exactness is already inherited
from the geometric adjunction, so this finite-colimit assertion supplies exactness. -/
theorem immersionClosedExact (Λ : ScalarSixRing.{u}) (k : Type u) [Field k]
    {Z X : Over (Spec (.of k))}
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    (i : Z ⟶ X) [IsClosedImmersion i.left] :
    PreservesFiniteColimits (lowerStar Λ.X i.left) := by
  let V : X.left.Opens :=
    ⟨(Set.range i.left)ᶜ, i.left.isClosedEmbedding.isClosed_range.isOpen_compl⟩
  have : IsLocallyNoetherian X.left :=
    LocallyOfFiniteType.isLocallyNoetherian X.hom
  have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  have : IsNoetherian X.left := ⟨⟩
  have : QuasiCompact V.ι := inferInstance
  exact closedSupport_lowerStarExact Λ.X i.left V.ι (by simp [V])

/-- The supplied open/closed factorization as an actual compactification.
Source: locally closed paragraph of the source
(blueprint: lem-sfb-immersion-projection-scalar-normalization). -/
def immersionCompactification {S Z X : Scheme.{u}} (j : S ⟶ Z) (i : Z ⟶ X)
    [IsOpenImmersion j] [IsClosedImmersion i] : Compactification (j ≫ i) where
  Z := Z
  i := j
  g := i
  comm := rfl
  isOpenImmersion := inferInstance
  isProper := inferInstance

/-- The canonical normalized identification Ri_* D(u_!) = D(i_*) D(u_!). Its data is the
published exact-functor comparison, not a choice of an isomorphism between the models.
Source: Stacks 09BM, 09BN; derived and locally closed paragraphs
(blueprint: lem-sfb-immersion-projection-scalar-normalization). -/
def immersionExtensionExact (Λ : ScalarSixRing.{u}) (k : Type u) [Field k]
    {S Z X : Over (Spec (.of k))}
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    (j : S ⟶ Z) (i : Z ⟶ X) [IsOpenImmersion j.left] [IsClosedImmersion i.left] :=
  letI := immersionClosedExact Λ k i
  Functor.isoWhiskerLeft (openImmersionLowerShriek Λ.X j.left).mapDerivedCategory
    (lowerStar Λ.X i.left).rightDerivedFunctorIsoMapDerivedCategory

/-- The four specified factors of rho, with the pullback compositor at the last target.
The inverse open factor is the inverse of the specified unit adjunct.
Source: locally closed paragraph of the source
(blueprint: lem-sfb-immersion-projection-scalar-normalization). -/
def immersionProjection (Λ : ScalarSixRing.{u}) (k : Type u) [Field k]
    {S Z X : Over (Spec (.of k))}
    [LocallyOfFiniteType S.hom] [QuasiCompact S.hom] [IsSeparated S.hom]
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
    (j : S ⟶ Z) (i : Z ⟶ X) [IsOpenImmersion j.left] [IsClosedImmersion i.left]
    (C : DerivedCategory (supportModules Λ.X X.left))
    (L : DerivedCategory (supportModules Λ.X S.left)) :
    C ⊗ (sfbScalarCompactModel Λ j.left i.left).obj L ⟶
      (sfbScalarCompactModel Λ j.left i.left).obj
        ((scalarSixPull Λ (j.left ≫ i.left)).obj C ⊗ L) :=
  letI := DerivedCategory.braidedCategory' (supportModules Λ.X X.left)
  letI := DerivedCategory.braidedCategory' (supportModules Λ.X Z.left)
  letI := immersionOpenProjection_isIso Λ k j L ((scalarSixPull Λ i.left).obj C)
  (β_ C ((sfbScalarCompactModel Λ j.left i.left).obj L)).hom ≫
    immersionClosedProjection Λ i.left
      ((openImmersionLowerShriek Λ.X j.left).mapDerivedCategory.obj L) C ≫
    (RootCoordinateFace.lower Λ.X i.left).map
      ((β_ ((openImmersionLowerShriek Λ.X j.left).mapDerivedCategory.obj L)
        ((scalarSixPull Λ i.left).obj C)).hom ≫
        inv (immersionOpenProjection Λ j.left L ((scalarSixPull Λ i.left).obj C)) ≫
        (openImmersionLowerShriek Λ.X j.left).mapDerivedCategory.map
          ((scalarSixPullComp Λ j.left i.left).inv.app C ⊗ₘ 𝟙 L))

/-- q_u defined by scalar adjunction, from the literal open coefficient-action square.
The d square is obtained by exact termwise descent of comapOpenImmersionLowerShriekIso.
Source: Stacks 09BN; coefficient normalization in the node
(blueprint: lem-sfb-immersion-projection-scalar-normalization). -/
def immersionOpenScalarMap {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ')
    {S Z : Scheme.{u}} (j : S ⟶ Z) [IsOpenImmersion j]
    (L : DerivedCategory (supportModules Λ.X S)) :
    (scalarSixChange a Z).obj ((openImmersionLowerShriek Λ.X j).mapDerivedCategory.obj L) ⟶
      (openImmersionLowerShriek Λ'.X j).mapDerivedCategory.obj ((scalarSixChange a S).obj L) :=
  let d := (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso
      (comapOpenImmersionLowerShriekIso (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom j) ≪≫
        Functor.mapDerivedCategoryCompIso _ _
  ((Mod.derivedExtendMapDerivedCategoryAdjunction
    (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom Z)).homEquiv _ _).symm
    ((openImmersionLowerShriek Λ.X j).mapDerivedCategory.map
      ((Mod.derivedExtendMapDerivedCategoryAdjunction
        (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom S)).unit.app L) ≫
      d.inv.app ((scalarSixChange a S).obj L))

/-- q_a is the ordinary counit-defined closed comparison, then i'_* of q_u.
Source: coefficient normalization and det-prop-scalar-six-compact-support
(blueprint: lem-sfb-immersion-projection-scalar-normalization). -/
def immersionScalarMap {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ')
    {S Z X : Scheme.{u}} (j : S ⟶ Z) (i : Z ⟶ X)
    [IsOpenImmersion j] [IsClosedImmersion i]
    (L : DerivedCategory (supportModules Λ.X S)) :
    (scalarSixChange a X).obj ((sfbScalarCompactModel Λ j i).obj L) ⟶
      (sfbScalarCompactModel Λ' j i).obj ((scalarSixChange a S).obj L) :=
  (scalarDirectImageMate a i).app
      ((openImmersionLowerShriek Λ.X j).mapDerivedCategory.obj L) ≫
    (RootCoordinateFace.lower Λ'.X i).map (immersionOpenScalarMap a j L)

/-- The closed projection/scalar square, with the existing K-flat scalar tensorator and
c_i inverse = theta_i. The local instances select the published scalar monoidal structure.
Source: Stacks 0B56 and 0E48; specified closed coefficient square
(blueprint: lem-sfb-immersion-projection-scalar-normalization). -/
def ImmersionClosedScalarSquare {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ')
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (B : DerivedCategory (supportModules Λ.X Z))
    (C : DerivedCategory (supportModules Λ.X X)) : Prop :=
  letI := Mod.extendScalarsMonoidal (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom X)
  letI := Mod.extendScalarsMonoidal (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom Z)
  let tX :=
    (Mod.extendScalars
      (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom X)).leftDerivedTensorComparison
  let tZ :=
    (Mod.extendScalars
      (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom Z)).leftDerivedTensorComparison
  (scalarSixChange a X).map (immersionClosedProjection Λ i B C) ≫
      (scalarDirectImageMate a i).app (B ⊗ (scalarSixPull Λ i).obj C) ≫
      (RootCoordinateFace.lower Λ'.X i).map
        ((tZ.app B).app ((scalarSixPull Λ i).obj C) ≫
          (𝟙 _ ⊗ₘ (scalarDirectImagePullbackData.theta a i).hom.app C)) =
    (tX.app ((RootCoordinateFace.lower Λ.X i).obj B)).app C ≫
      ((scalarDirectImageMate a i).app B ⊗ₘ 𝟙 _) ≫
      immersionClosedProjection Λ' i ((scalarSixChange a Z).obj B)
        ((scalarSixChange a X).obj C)

/-- The open projection/scalar square in the direction of the specified sigma.
Source: Stacks 0E8I and 0E48; open-unit calculation in the node
(blueprint: lem-sfb-immersion-projection-scalar-normalization). -/
def ImmersionOpenScalarSquare {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ')
    {S Z : Scheme.{u}} (j : S ⟶ Z) [IsOpenImmersion j]
    (D : DerivedCategory (supportModules Λ.X Z))
    (L : DerivedCategory (supportModules Λ.X S)) : Prop :=
  letI := Mod.extendScalarsMonoidal (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom Z)
  letI := Mod.extendScalarsMonoidal (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom S)
  let tZ :=
    (Mod.extendScalars
      (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom Z)).leftDerivedTensorComparison
  let tS :=
    (Mod.extendScalars
      (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom S)).leftDerivedTensorComparison
  (scalarSixChange a Z).map (immersionOpenProjection Λ j L D) ≫
      (tZ.app D).app ((openImmersionLowerShriek Λ.X j).mapDerivedCategory.obj L) ≫
      (𝟙 _ ⊗ₘ immersionOpenScalarMap a j L) =
    immersionOpenScalarMap a j ((scalarSixPull Λ j).obj D ⊗ L) ≫
      (openImmersionLowerShriek Λ'.X j).mapDerivedCategory.map
        ((tS.app ((scalarSixPull Λ j).obj D)).app L ≫
          ((scalarDirectImagePullbackData.theta a j).hom.app D ⊗ₘ 𝟙 _)) ≫
      immersionOpenProjection Λ' j ((scalarSixChange a S).obj L)
        ((scalarSixChange a Z).obj D)

/-- The displayed equation for rho and q_a; mu is t_S followed by c_a inverse tensor 1.
The definition expands to an equality between the two specified composites, with no
additional comparison or unspecified natural isomorphism as input.
Source: locally closed paragraph and explicit coefficient square in the node
(blueprint: lem-sfb-immersion-projection-scalar-normalization). -/
def ImmersionProjectionScalarSquare {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ')
    (k : Type u) [Field k] {S Z X : Over (Spec (.of k))}
    [LocallyOfFiniteType S.hom] [QuasiCompact S.hom] [IsSeparated S.hom]
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
    (j : S ⟶ Z) (i : Z ⟶ X) [IsOpenImmersion j.left] [IsClosedImmersion i.left]
    (C : DerivedCategory (supportModules Λ.X X.left))
    (L : DerivedCategory (supportModules Λ.X S.left)) : Prop :=
  letI := Mod.extendScalarsMonoidal (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom X.left)
  letI := Mod.extendScalarsMonoidal (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom S.left)
  let tX :=
    (Mod.extendScalars
      (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom X.left)).leftDerivedTensorComparison
  let tS :=
    (Mod.extendScalars
      (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom S.left)).leftDerivedTensorComparison
  (scalarSixChange a X.left).map (immersionProjection Λ k j i C L) ≫
      immersionScalarMap a j.left i.left ((scalarSixPull Λ (j.left ≫ i.left)).obj C ⊗ L) ≫
      (sfbScalarCompactModel Λ' j.left i.left).map
        ((tS.app ((scalarSixPull Λ (j.left ≫ i.left)).obj C)).app L ≫
          ((scalarDirectImagePullbackData.theta a (j.left ≫ i.left)).hom.app C ⊗ₘ 𝟙 _)) =
    (tX.app C).app ((sfbScalarCompactModel Λ j.left i.left).obj L) ≫
      (𝟙 _ ⊗ₘ immersionScalarMap a j.left i.left L) ≫
      immersionProjection Λ' k j i ((scalarSixChange a X.left).obj C)
        ((scalarSixChange a S.left).obj L)

/-- The specified immersion projections are invertible and commute with listed changes
of coefficients, and q_a is the compact-support comparison on Dctf.
Source: blueprint latest, det-lem-int-tensor-projection.proof.md, all four paragraphs;
Stacks 0E8I, 0B56, 0E48, 09BM and 09BN
(blueprint: lem-sfb-immersion-projection-scalar-normalization).

Proof:
1. The standing schemes are Noetherian by finite type over k. Every open is quasi-compact
by lem-sfb-noetherian-space-compact-subsets. Exact immersion extension and exact-functor
derived factorization identify Ri_* D(u_!) with the exact E, in both coefficient rings.
2. The closed projection is the closed adjunction transpose of t_i followed by counit
 tensor identity. By lem-weil-pbc-adjunct-counit-identity it is the published closed
support projection after canonical transport. The open map is the corresponding symmetry
conjugate. lem-sfb-condensed-support-projection-formula makes both invertible for every
unbounded input. Their composite, the two symmetries and pullback compositor give rho.
On flat-term K-flat representatives these maps are termwise the sheaf maps of 0E8I;
lem-weil-pbc-ringed-topoi-derived-tensor-pullback and
lem-sf-exact-localization-inverse-mate preserve this normalization upon localization.
3. Descend the literal open coefficient-action square termwise. Its open mate is the
inverse restriction/pullback square. Paste with the scalar adjunction using
lem-weil-pbc-mate-pasting. The scalar adjunct is exactly u_! eta followed by d inverse,
so q_u equals derivedOpenImmersionShriekIso, without a flatness hypothesis.
4. Regard scalar extension as pullback of the identity ringed topos.
lem-sfb-ringed-derived-monoidal-comparisons and
lem-sfb-kflat-scalar-comparison-normalization identify its monoidal comparisons with t
and c. lem-sfb-ringed-comparison-tensor-adjunction identifies its closed exchange with
scalarDirectImageMate. lem-weil-pbc-ringed-exchange-tensor-coherence gives the closed
square for this actual counit-defined comparison, without assuming it invertible.
5. The unit equation of lem-weil-pbc-conjugate-iso-unit-equation identifies the open
restriction of q_u with the scalar extension of the open unit. Transpose both routes of
the open square. Substitute sigma's defining unit adjunct. Naturality of t and
monoidality of c make both adjuncts t followed by c inverse tensor identity, the open
unit and inverse pullback tensorator. Injectivity of the Hom bijection gives equality.
6. Expand rho and q_a. Commute T past the symmetries, apply the closed square and the
inverse of the open square, then use naturality of the closed mate. Paste with the
monoidal pullback compositor. The surviving inside comparison is precisely mu; this is
the stated equality, not merely existence of a comparison isomorphism.
7. The closed counit equation for gamma_i shows i'^* gamma_i invertible. On the open
complement both endpoints vanish, since scalar extension commutes with restriction.
Joint detection in lem-sfb-condensed-support-derived-localization makes gamma_i
invertible on every unbounded input. Thus q_a is invertible, in particular on Dctf.
The defining compact-support composite is gamma_i followed by i'_* of the open
conjugate. Step 3 identifies it with q_a. This uses neither general scalar-six
isomorphism theorem, whose field-dimension hypothesis is unnecessary for immersions. -/
theorem immersionProjectionScalarNormalization (ell : ℕ) [Fact ell.Prime]
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ') (_ha : ListedCoefficientMap ell a)
    {S Z X : Over (Spec (.of k))}
    [LocallyOfFiniteType S.hom] [QuasiCompact S.hom] [IsSeparated S.hom]
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    (j : S ⟶ Z) (i : Z ⟶ X) [IsOpenImmersion j.left] [IsClosedImmersion i.left] :
    (∀ (B : DerivedCategory (supportModules Λ.X Z.left))
      (C : DerivedCategory (supportModules Λ.X X.left)),
      IsIso (immersionClosedProjection Λ i.left B C)) ∧
    (∀ (B : DerivedCategory (supportModules Λ'.X Z.left))
      (C : DerivedCategory (supportModules Λ'.X X.left)),
      IsIso (immersionClosedProjection Λ' i.left B C)) ∧
    (∀ (C : DerivedCategory (supportModules Λ.X X.left))
      (L : DerivedCategory (supportModules Λ.X S.left)),
      IsIso (immersionProjection Λ k j i C L)) ∧
    (∀ (C : DerivedCategory (supportModules Λ'.X X.left))
      (L : DerivedCategory (supportModules Λ'.X S.left)),
      IsIso (immersionProjection Λ' k j i C L)) ∧
    (∀ L : DerivedCategory (supportModules Λ.X S.left),
      immersionOpenScalarMap a j.left L =
        (derivedOpenImmersionShriekIso (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom j.left).hom.app L) ∧
    (∀ (B : DerivedCategory (supportModules Λ.X Z.left))
      (C : DerivedCategory (supportModules Λ.X X.left)),
      ImmersionClosedScalarSquare a i.left B C) ∧
    (∀ (D : DerivedCategory (supportModules Λ.X Z.left))
      (L : DerivedCategory (supportModules Λ.X S.left)),
      ImmersionOpenScalarSquare a j.left D L) ∧
    (∀ (C : DerivedCategory (supportModules Λ.X X.left))
      (L : DerivedCategory (supportModules Λ.X S.left)),
      ImmersionProjectionScalarSquare a k j i C L) ∧
    (∀ L : ConstantModelConstructibleFiniteTor Λ.X S.left,
      IsIso (immersionScalarMap a j.left i.left L.obj) ∧
        immersionScalarMap a j.left i.left L.obj =
          (scalarCompactSupportMap a j.left i.left).app L.obj) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
