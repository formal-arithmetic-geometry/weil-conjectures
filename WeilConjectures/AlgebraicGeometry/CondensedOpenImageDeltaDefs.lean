/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
public import Mathlib.Algebra.Homology.ExactSequence
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.CategoryTheory.Monoidal.CommMon_
public import Mathlib.CategoryTheory.Monoidal.Mon
public import WeilConjectures.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.CategoryTheory.RightDerivedSingleH0
public import WeilConjectures.AlgebraicGeometry.BoundedConstructiblePushforwardRestriction
public import WeilConjectures.AlgebraicGeometry.CoefficientHeart
public import WeilConjectures.AlgebraicGeometry.CondensedModuleDerivedPushpull
public import WeilConjectures.AlgebraicGeometry.CondensedStrictWeilComplex
public import WeilConjectures.AlgebraicGeometry.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.DeligneLaumon.AffineLine.Defs
public import WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.BaseChange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs

/-! # Definitions for condensed open image delta

The definitions used by the condensed open-image theorem are kept in this
foundational module so that each proof component can be stated in its own module.
They are re-exported by `WeilConjectures.AlgebraicGeometry.CondensedOpenImageDelta`.

Source: latest blueprint, p-dl-a1-exact, Steps 1--2
(blueprint: new-dl-a1-defs).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ] {U C : Scheme.{u}} (j : U ⟶ C)

/-- The boundary from the image of the canonical geometric short-exact triangle,
with its source identified by the canonical zeroth-derived comparison.
Source: latest blueprint, p-dl-a1-exact, Step 1
(blueprint: lem-dl-a1-condensed-open-image-delta). -/
def dlOpenImageDelta
    (S : ShortComplex (Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
      (condensedRingObj Λ U))) (hS : S.ShortExact) :
    (lowerStar Λ j).obj S.X₃ ⟶
      (DerivedCategory.homologyFunctor _ 1).obj
        ((moduleObjectDerivedPushforward Λ j).obj
          ((DerivedCategory.singleFunctor _ 0).obj S.X₁)) :=
  ((lowerStar Λ j).singleRightDerivedH0Iso S.X₃).inv ≫
    DerivedCategory.HomologySequence.δ
      ((lowerStar Λ j).rightDerivedFunctor.mapTriangle.obj hS.singleTriangle) 0 1 rfl

/-- The derived square comparison is the canonical composition comparison.
Taking its right mate gives the Frobenius exchange used on direct images.
This construction needs only commutativity; the Frobenius squares are cartesian.
Source: latest blueprint, p-dl-a1-exact, Steps 1--2; lem-fix-weil-operations
(blueprint: lem-dl-a1-condensed-open-image-delta). -/
def dlOpenImageExchange {gU : U ⟶ U} {gC : C ⟶ C}
    (sq : CommSq gU j j gC) :
    moduleObjectDerivedPushforward Λ j ⋙ moduleObjectDerivedPullback Λ gC ⟶
      moduleObjectDerivedPullback Λ gU ⋙ moduleObjectDerivedPushforward Λ j :=
  Adjunction.exchangeRight (derivedUpperStarLowerStarAdjunction Λ j)
    (derivedUpperStarLowerStarAdjunction Λ j)
    ((leftDerivedUpperStarComp Λ j gC).symm ≪≫
      (upperStar Λ (j ≫ gC)).leftDerivedFunctorNatIso
        (upperStarCongr Λ sq.w.symm) ≪≫ leftDerivedUpperStarComp Λ gU j)

/-- The ordinary direct-image Weil map, with the specified coefficient mate.
Source: latest blueprint, p-dl-a1-exact, Step 1; lem-fix-weil-operations
(blueprint: lem-dl-a1-condensed-open-image-delta). -/
def dlOpenImageWeilMap {gU : U ⟶ U} {gC : C ⟶ C}
    (sq : CommSq gU j j gC)
    (M : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ U))
    (φ : (upperStar Λ gU).obj M ≅ M) :
    (upperStar Λ gC).obj ((lowerStar Λ j).obj M) ⟶ (lowerStar Λ j).obj M :=
  (lowerStarBaseChange Λ sq).app M ≫ (lowerStar Λ j).map φ.hom

/-- The derived direct-image Weil map: exact single comparison, canonical exchange,
and the image of the given degree-zero Weil structure.
Source: latest blueprint, p-dl-a1-exact, Step 1; lem-fix-weil-operations
(blueprint: lem-dl-a1-condensed-open-image-delta). -/
def dlOpenImageDerivedWeilMap {gU : U ⟶ U} {gC : C ⟶ C}
    (sq : CommSq gU j j gC)
    (M : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ U))
    (φ : (upperStar Λ gU).obj M ≅ M) :
    (moduleObjectDerivedPullback Λ gC).obj
        ((moduleObjectDerivedPushforward Λ j).obj
          ((DerivedCategory.singleFunctor _ 0).obj M)) ⟶
      (moduleObjectDerivedPushforward Λ j).obj
        ((DerivedCategory.singleFunctor _ 0).obj M) :=
  (dlOpenImageExchange Λ j sq).app ((DerivedCategory.singleFunctor _ 0).obj M) ≫
    (moduleObjectDerivedPushforward Λ j).map
      ((leftDerivedUpperStarIsoMapDerivedCategory Λ gU).hom.app
          ((DerivedCategory.singleFunctor _ 0).obj M) ≫
        ((upperStar Λ gU).mapDerivedCategorySingleFunctor 0).hom.app M ≫
        (DerivedCategory.singleFunctor _ 0).map φ.hom)

/-- The induced Weil map on cohomology, using exact inverse image and its canonical
homology comparison. Source: latest blueprint, p-dl-a1-exact, Step 1
(blueprint: lem-dl-a1-condensed-open-image-delta). -/
def dlOpenImageHomologyWeilMap {gU : U ⟶ U} {gC : C ⟶ C}
    (sq : CommSq gU j j gC)
    (M : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ U))
    (φ : (upperStar Λ gU).obj M ≅ M) (r : ℤ) :
    (upperStar Λ gC).obj ((DerivedCategory.homologyFunctor _ r).obj
        ((moduleObjectDerivedPushforward Λ j).obj
          ((DerivedCategory.singleFunctor _ 0).obj M))) ⟶
      (DerivedCategory.homologyFunctor _ r).obj
        ((moduleObjectDerivedPushforward Λ j).obj
          ((DerivedCategory.singleFunctor _ 0).obj M)) :=
  ((upperStar Λ gC).mapDerivedCategoryHomologyFunctorIso r).hom.app
      ((moduleObjectDerivedPushforward Λ j).obj
        ((DerivedCategory.singleFunctor _ 0).obj M)) ≫
    (DerivedCategory.homologyFunctor _ r).map
      ((leftDerivedUpperStarIsoMapDerivedCategory Λ gC).inv.app
          ((moduleObjectDerivedPushforward Λ j).obj
            ((DerivedCategory.singleFunctor _ 0).obj M)) ≫
        dlOpenImageDerivedWeilMap Λ j sq M φ)

/-- The geometric assertions, with the ordinary direct-image arrows and actual counit.
The exactness assertion includes the initial zero by monicity of the first arrow.
Naturality is in every morphism of constructible short exact sequences.
Source: latest blueprint, p-dl-a1-exact, Steps 1--2
(blueprint: lem-dl-a1-condensed-open-image-delta). -/
def DlOpenImageAssertions : Prop :=
  (∀ M : ConstantModelConstructible Λ U,
    (∀ r : ℤ, r < 0 → IsZero ((DerivedCategory.homologyFunctor _ r).obj
      ((moduleObjectDerivedPushforward Λ j).obj
        ((DerivedCategory.singleFunctor _ 0).obj M.obj)))) ∧
    ((DerivedCategory.homologyFunctor _ 0).map
        ((lowerStar Λ j).singleRightDerivedUnit.app M.obj) ≫
      ((lowerStar Λ j).singleRightDerivedH0Iso M.obj).hom =
        (DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).hom.app
          ((lowerStar Λ j).obj M.obj)) ∧
    IsConstantModelConstructible Λ C ((lowerStar Λ j).obj M.obj) ∧
    (∀ r : ℤ, IsConstantModelConstructible Λ C
      ((DerivedCategory.homologyFunctor _ r).obj
        ((moduleObjectDerivedPushforward Λ j).obj
          ((DerivedCategory.singleFunctor _ 0).obj M.obj)))) ∧
    (∀ r : ℤ, 0 < r → IsZero ((upperStar Λ j).obj
      ((DerivedCategory.homologyFunctor _ r).obj
        ((moduleObjectDerivedPushforward Λ j).obj
          ((DerivedCategory.singleFunctor _ 0).obj M.obj)))))) ∧
  (∀ K : ConstantModelBoundedConstructible Λ U,
    IsIso ((derivedUpperStarLowerStarAdjunction Λ j).counit.app K.obj)) ∧
  (∀ (S : ShortComplex (Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
      (condensedRingObj Λ U))) (hS : S.ShortExact),
    IsConstantModelConstructible Λ U S.X₁ →
    IsConstantModelConstructible Λ U S.X₂ →
    IsConstantModelConstructible Λ U S.X₃ →
    Mono ((lowerStar Λ j).map S.f) ∧
      (ComposableArrows.mk₃ ((lowerStar Λ j).map S.f) ((lowerStar Λ j).map S.g)
        (dlOpenImageDelta Λ j S hS)).Exact) ∧
  (∀ (S T : ShortComplex (Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
      (condensedRingObj Λ U))) (hS : S.ShortExact) (hT : T.ShortExact) (τ : S ⟶ T),
    IsConstantModelConstructible Λ U S.X₁ →
    IsConstantModelConstructible Λ U S.X₂ →
    IsConstantModelConstructible Λ U S.X₃ →
    IsConstantModelConstructible Λ U T.X₁ →
    IsConstantModelConstructible Λ U T.X₂ →
    IsConstantModelConstructible Λ U T.X₃ →
    (lowerStar Λ j).map τ.τ₃ ≫ dlOpenImageDelta Λ j T hT =
      dlOpenImageDelta Λ j S hS ≫
        (DerivedCategory.homologyFunctor _ 1).map
          ((moduleObjectDerivedPushforward Λ j).map
            ((DerivedCategory.singleFunctor _ 0).map τ.τ₁)))

/-- Equivariance of every arrow, including the connecting map, for the canonical
operation structures. Structures on the higher image are induced on cohomology.
Source: latest blueprint, p-dl-a1-exact, Step 1; lem-fix-weil-operations
(blueprint: lem-dl-a1-condensed-open-image-delta). -/
def DlOpenImageWeilAssertions {gU : U ⟶ U} {gC : C ⟶ C}
    (sq : CommSq gU j j gC) : Prop :=
  ∀ (S : ShortComplex (Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
      (condensedRingObj Λ U))) (hS : S.ShortExact),
    IsConstantModelConstructible Λ U S.X₁ →
    IsConstantModelConstructible Λ U S.X₂ →
    IsConstantModelConstructible Λ U S.X₃ →
    ∀ (φ₁ : (upperStar Λ gU).obj S.X₁ ≅ S.X₁)
      (φ₂ : (upperStar Λ gU).obj S.X₂ ≅ S.X₂)
      (φ₃ : (upperStar Λ gU).obj S.X₃ ≅ S.X₃),
    (upperStar Λ gU).map S.f ≫ φ₂.hom = φ₁.hom ≫ S.f →
    (upperStar Λ gU).map S.g ≫ φ₃.hom = φ₂.hom ≫ S.g →
    IsIso (dlOpenImageWeilMap Λ j sq S.X₁ φ₁) ∧
    IsIso (dlOpenImageWeilMap Λ j sq S.X₂ φ₂) ∧
    IsIso (dlOpenImageWeilMap Λ j sq S.X₃ φ₃) ∧
    IsIso (dlOpenImageHomologyWeilMap Λ j sq S.X₁ φ₁ 1) ∧
    (upperStar Λ gC).map ((lowerStar Λ j).map S.f) ≫
        dlOpenImageWeilMap Λ j sq S.X₂ φ₂ =
      dlOpenImageWeilMap Λ j sq S.X₁ φ₁ ≫ (lowerStar Λ j).map S.f ∧
    (upperStar Λ gC).map ((lowerStar Λ j).map S.g) ≫
        dlOpenImageWeilMap Λ j sq S.X₃ φ₃ =
      dlOpenImageWeilMap Λ j sq S.X₂ φ₂ ≫ (lowerStar Λ j).map S.g ∧
    (upperStar Λ gC).map (dlOpenImageDelta Λ j S hS) ≫
        dlOpenImageHomologyWeilMap Λ j sq S.X₁ φ₁ 1 =
      dlOpenImageWeilMap Λ j sq S.X₃ φ₃ ≫ dlOpenImageDelta Λ j S hS

/-- The open immersion on the chosen geometric fibers is the existing slice
base-change functor on the given model morphism.
Source: latest blueprint, p-dl-a1-exact, Steps 1--2
(blueprint: lem-dl-a1-condensed-open-image-delta). -/
def dlGeometricOpen (D : WeilConjectures.FiniteFieldDatum.{u})
    {U₀ C₀ : Over (Spec (.of D.k₀))} (j₀ : U₀ ⟶ C₀) :=
  ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map j₀).left

end AlgebraicGeometry.ProEtale.CondensedRing
