/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ProfiniteCondensedRing
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
public import WeilConjectures.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor
public import WeilConjectures.RingTheory.ProEtale.WContractible
public import WeilConjectures.ProEtaleCoefficients.ConnectedComponentsProfinite
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedScalarRealization
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedLisseEvaluationModel
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ZetaWeil.ContractibleLisseEvaluation
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Functor.Flat
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Component.ComponentPointMonoidalFactorization
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Component.ComponentDerivedSymmetry
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Component.ComponentSectionRealization
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Component.ComponentLisseEquivalence
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Component.ComponentFinalScalarComparison
public import WeilConjectures.CategoryTheory.Cochain.CochainDerivedAdjunction
public import WeilConjectures.SmoothPurity.SheafRingCoefficientOrdinaryAdjunction
public import WeilConjectures.AlgebraicGeometry.Picard.KFlatResolutionIndependentCoefficients
public import WeilConjectures.CategoryTheory.RingedKFlatWord.RingedKFlatWordComparisonDescent
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ZetaWeil.ProfiniteCoefficientSliceBaseChange
public import WeilConjectures.CategoryTheory.ZetaWeil.ContractibleDerivedSectionsTensor
public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
public import WeilConjectures.AlgebraicGeometry.ComponentDerivedSquare.ComponentDerivedPullbackSquare
public import WeilConjectures.RingTheory.ProperBaseChange.IndEtaleUniverseTransport
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Topology.Irreducible


/-! # Generic scalar models on prescribed w-contractible affine covers

Source: Hemo--Richarz--Scholbach, Constructible sheaves on schemes, Theorem 4.13,
irreducible case, diagram (4.4) and its following paragraph; Lemma 4.1 and
Proposition 4.3(3) (blueprint: lem-zl-condensed-irreducible-generic-scalar-model).
The unchanged data are recorded by
(blueprint: def-zl-condensed-generic-scalar-model-data).
- Our auxiliary data package records the component descent and its compatibility with
  the originally fixed generic isomorphism. Every functor is an existing inverse image.
- The section clause records the isomorphism obtained by pulling back that very descent.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits Opposite Topology
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

namespace CondensedGenericScalarModel

/-- The canonical identification of the two restrictions to the generic fibre, obtained
from the ordinary derived composition comparisons and the pullback square equality.
Source: HRS Theorem 4.13, (4.4)
(blueprint: lem-zl-condensed-irreducible-generic-scalar-model). -/
def genericRestriction (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    {X U : Scheme.{u}} (f : U ⟶ X) (Ω : Type u) [Field Ω]
    (η : Spec (.of Ω) ⟶ X)
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ.X X))) :
    (CondensedRing.upperStar Λ.X (pullback.fst f η)).mapDerivedCategory.obj
        ((CondensedRing.upperStar Λ.X f).mapDerivedCategory.obj K) ≅
      (CondensedRing.upperStar Λ.X (pullback.snd f η)).mapDerivedCategory.obj
        ((CondensedRing.upperStar Λ.X η).mapDerivedCategory.obj K) :=
  ((ComponentDerivedSquare.schemeComposition Λ f (pullback.fst f η)).app K).symm ≪≫
    eqToIso (congrArg
      (fun a => (CondensedRing.upperStar Λ.X a).mapDerivedCategory.obj K)
      (pullback.condition (f := f) (g := η))) ≪≫
    (ComponentDerivedSquare.schemeComposition Λ η (pullback.snd f η)).app K

/-- The common point-valued part of the existing scalar realization, before inverse image.
This is a transparent intermediate composite of the recorded scalar-realization construction.
Source: HRS Definition 3.5 (blueprint: lem-zl-condensed-irreducible-generic-scalar-model). -/
def pointRealization (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X] :=
  let e := InternalAbelianSheafModule.sectionModuleEquivalence
    (coherentTopology Profinite.{u}) Λ.X
  letI := Functor.additive_of_preserves_binary_products e.inverse
  commutativeSiteDerivedConstantModuleFunctor (coherentTopology Profinite.{u})
      (condensedScalarRing Λ.X) ⋙
    (condensedScalarExtensionModel Λ.X).T ⋙ e.inverse.mapDerivedCategory

/-- The scalar comparison is the localization of the specified ordinary comparison,
precomposed with the common point realization. No arbitrary derived map is selected.
Source: HRS Theorem 4.13 (blueprint: lem-zl-condensed-irreducible-generic-scalar-model). -/
def cornerScalarComparison (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    (T : Scheme.{u}) [IsAffine T] (c : ComponentDerivedSquare.Corner Λ T)
    (ordinary : ((coherentTopology Profinite.{u}).overPullback Ab.{u + 1}
        (affineComponentSpace T)).mapMod Λ.X ⋙ c.modules Λ T ≅
      (upperStarFromPoint T).mapMod Λ.X) :
    CondensedRing.profiniteScalarRealization Λ.X (affineComponentSpace T) ⋙
      c.derived Λ T ≅ condensedScalarRealization Λ.X T := by
  unfold ComponentDerivedSquare.Corner.derived
  exact
    Functor.isoWhiskerLeft (pointRealization Λ)
      ((Functor.mapDerivedCategoryCompIso
        (((coherentTopology Profinite.{u}).overPullback Ab.{u + 1}
          (affineComponentSpace T)).mapMod Λ.X) (c.modules Λ T)).symm ≪≫
        Functor.mapDerivedCategoryNatIso ordinary)

/-- The scheme scalar comparison is likewise the localization of its specified ordinary
module comparison, before precomposition with the point realization.
Source: HRS Theorem 4.13 (blueprint: lem-zl-condensed-irreducible-generic-scalar-model). -/
def schemeScalarComparison (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    {T V : Scheme.{u}} (h : V ⟶ T)
    (ordinary : (upperStarFromPoint T).mapMod Λ.X ⋙ CondensedRing.upperStar Λ.X h ≅
      (upperStarFromPoint V).mapMod Λ.X) :
    condensedScalarRealization Λ.X T ⋙
      (CondensedRing.upperStar Λ.X h).mapDerivedCategory ≅
    condensedScalarRealization Λ.X V :=
  Functor.isoWhiskerLeft (pointRealization Λ)
    ((Functor.mapDerivedCategoryCompIso ((upperStarFromPoint T).mapMod Λ.X)
      (CondensedRing.upperStar Λ.X h)).symm ≪≫ Functor.mapDerivedCategoryNatIso ordinary)

/-- Canonically normalized identity and scalar comparisons for a section of a component map.
The test-object projection fixes the underlying identity comparison via its adjunction mate;
the scalar comparison has underlying map the slice's absolute-test comparison.
Source: HRS Theorem 4.13, after (4.4)
(blueprint: lem-zl-condensed-irreducible-generic-scalar-model). -/
structure SectionComparison (Λ : Profinite.CondensedRing.{u})
    {S V : Profinite.{u}} (r : V ⟶ S) (s : S ⟶ V)
    (restriction : ComponentDerivedSquare.Slice Λ r) where
  inverse : ComponentDerivedSquare.Slice Λ s
  tests : Over.pullback r ⋙ Over.pullback s ≅ 𝟭 (Over S)
  tests_projection : ∀ E : Over S, (tests.hom.app E).left =
    pullback.fst ((Over.pullback r).obj E).hom s ≫ pullback.fst E.hom r
  abelian : restriction.inverse ⋙ inverse.inverse ≅ 𝟭 _
  abelian_mate : ∀ (G : Sheaf ((coherentTopology Profinite.{u}).over S) Ab.{u + 1}) E,
    (((conjugateIsoEquiv
      (restriction.adjunction.comp inverse.adjunction) (Adjunction.id)
      abelian.symm).hom.app G).hom.app (op E)) = G.obj.map (tests.inv.app E).op
  ordinary : restriction.modules Λ ⋙ inverse.modules Λ ≅ 𝟭 _
  ordinary_underlying : ∀ M, (ordinary.hom.app M).hom = abelian.hom.app M.X
  scalar : ((coherentTopology Profinite.{u}).overPullback Ab.{u + 1} V).mapMod Λ.X ⋙
      inverse.modules Λ ≅
    ((coherentTopology Profinite.{u}).overPullback Ab.{u + 1} S).mapMod Λ.X
  scalar_underlying : ∀ M, (scalar.hom.app M).hom = inverse.beta.hom.app M.X

/-- The identity comparison on derived objects is the localization of the normalized
ordinary comparison in the section data.
Source: HRS Theorem 4.13 (blueprint: lem-zl-condensed-irreducible-generic-scalar-model). -/
def SectionComparison.identityDerived (Λ : Profinite.CondensedRing.{u})
    {S V : Profinite.{u}} {r : V ⟶ S} {s : S ⟶ V}
    {restriction : ComponentDerivedSquare.Slice Λ r}
    (c : SectionComparison Λ r s restriction) :
    restriction.derived Λ ⋙ c.inverse.derived Λ ≅ 𝟭 _ := by
  unfold ComponentDerivedSquare.Slice.derived
  exact
    (Functor.mapDerivedCategoryCompIso (restriction.modules Λ) (c.inverse.modules Λ)).symm ≪≫
      Functor.mapDerivedCategoryNatIso c.ordinary ≪≫ Functor.mapDerivedCategoryIdIso _

/-- The scalar comparison on derived objects is the localization of the absolute-test
comparison, with the same fixed scalar complex as before restriction.
Source: HRS Theorem 4.13 (blueprint: lem-zl-condensed-irreducible-generic-scalar-model). -/
def SectionComparison.scalarDerived (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    {S V : Profinite.{u}} {r : V ⟶ S} {s : S ⟶ V}
    {restriction : ComponentDerivedSquare.Slice Λ r}
    (c : SectionComparison Λ r s restriction) :
    CondensedRing.profiniteScalarRealization Λ.X V ⋙ c.inverse.derived Λ ≅
      CondensedRing.profiniteScalarRealization Λ.X S := by
  unfold ComponentDerivedSquare.Slice.derived
  exact
    Functor.isoWhiskerLeft (pointRealization Λ)
      ((Functor.mapDerivedCategoryCompIso
        (((coherentTopology Profinite.{u}).overPullback Ab.{u + 1} V).mapMod Λ.X)
        (c.inverse.modules Λ)).symm ≪≫ Functor.mapDerivedCategoryNatIso c.scalar)

/-- Witnesses for the more precise component/section assertion. The corners and slice
pullbacks have their canonical coefficient comparisons, normalized by absolute test objects
in `ComponentDerivedSquare.Corner` and `ComponentDerivedSquare.Slice`. The equality
`generic_induced` says that delta is the descent of the restriction of the fixed alpha.
`sections` expresses pullback of that delta along every splitting, using the natural
identity and scalar composition comparisons, rather than choosing a new perfect model.
Source: HRS Theorem 4.13, diagram (4.4) and the following paragraph
(blueprint: lem-zl-condensed-irreducible-generic-scalar-model). -/
structure CoverModel (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    {X U : Scheme.{u}} [IsAffine X] [IsAffine U] (f : U ⟶ X)
    (Ω : Type u) [Field Ω] (η : Spec (.of Ω) ⟶ X)
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ.X X)))
    (P : DerivedCategory (ModuleCat.{u + 1} (condensedScalarRing Λ.X)))
    (α : (CondensedRing.upperStar Λ.X η).mapDerivedCategory.obj K ≅
      (condensedScalarRealization Λ.X (Spec (.of Ω))).obj P) where
  cornerU : ComponentDerivedSquare.Corner Λ U
  cornerV : ComponentDerivedSquare.Corner Λ (pullback f η)
  restriction : ComponentDerivedSquare.Slice Λ (affineComponentMap (pullback.fst f η))
  square : ComponentDerivedSquare.Square Λ (pullback.fst f η) cornerU cornerV restriction
  scalarV : ((coherentTopology Profinite.{u}).overPullback Ab.{u + 1}
      (affineComponentSpace (pullback f η))).mapMod Λ.X ⋙
      cornerV.modules Λ (pullback f η) ≅ (upperStarFromPoint (pullback f η)).mapMod Λ.X
  scalarV_underlying : ∀ N, (scalarV.hom.app N).hom = cornerV.beta.hom.app N.X
  scalarH : (upperStarFromPoint (Spec (.of Ω))).mapMod Λ.X ⋙
      CondensedRing.upperStar Λ.X (pullback.snd f η) ≅
    (upperStarFromPoint (pullback f η)).mapMod Λ.X
  scalarH_underlying : ∀ N, (scalarH.hom.app N).hom =
    (ComponentDerivedSquare.schemeUnderlying Λ (pullback.snd f η)).hom.app
        (((upperStarFromPoint (Spec (.of Ω))).mapMod Λ.X).obj N) ≫
      (upperStarFromPointComp (pullback.snd f η)).hom.app N.X
  M : CondensedRing.Evaluation.D
    ((coherentTopology Profinite.{u}).over (affineComponentSpace U))
    (CondensedRing.profiniteCoefficient Λ.X (affineComponentSpace U))
  dualizable : Nonempty (HasRightDual M)
  beta : (cornerU.derived Λ U).obj M ≅
    (CondensedRing.upperStar Λ.X f).mapDerivedCategory.obj K
  delta : (restriction.derived Λ).obj M ≅
    (CondensedRing.profiniteScalarRealization Λ.X (affineComponentSpace (pullback f η))).obj P
  generic_induced : (cornerV.derived Λ (pullback f η)).mapIso delta ≪≫
      (cornerScalarComparison Λ (pullback f η) cornerV scalarV).app P =
    (square.theta Λ).symm.app M ≪≫
      (CondensedRing.upperStar Λ.X (pullback.fst f η)).mapDerivedCategory.mapIso beta ≪≫
      genericRestriction Λ f Ω η K ≪≫
      (CondensedRing.upperStar Λ.X (pullback.snd f η)).mapDerivedCategory.mapIso α ≪≫
      (schemeScalarComparison Λ (pullback.snd f η) scalarH).app P
  splitting : ∃ s : affineComponentSpace U ⟶ affineComponentSpace (pullback f η),
    s ≫ affineComponentMap (pullback.fst f η) = 𝟙 (affineComponentSpace U)
  sections : ∀ (s : affineComponentSpace U ⟶ affineComponentSpace (pullback f η)),
    s ≫ affineComponentMap (pullback.fst f η) = 𝟙 (affineComponentSpace U) →
    ∃ (c : SectionComparison Λ (affineComponentMap (pullback.fst f η)) s restriction)
      (γ : M ≅ (CondensedRing.profiniteScalarRealization Λ.X (affineComponentSpace U)).obj P),
      (c.inverse.derived Λ).mapIso delta ≪≫ (c.scalarDerived Λ).app P =
        (c.identityDerived Λ).app M ≪≫ γ
  model : (CondensedRing.upperStar Λ.X f).mapDerivedCategory.obj K ≅
    (condensedScalarRealization Λ.X U).obj P

end CondensedGenericScalarModel

end AlgebraicGeometry.ProEtale
