/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q26
-/
module

public import Sheaf.Paper.CondensedModuleDerivedPushpull
public import Sheaf.AlgebraicGeometry.CondensedLisseProEtaleLocality
public import WeilConjectures.AlgebraicGeometry.ProEtale.AffineClosedSiteFunctorProperties
public import WeilConjectures.RingTheory.ProEtale.WContractible
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.GlobalSections
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import Sheaf.CategoryTheory.AdjunctionSquareExchange
public import Sheaf.Paper.CondensedQcqsPushforwardContinuity
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback

import Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.Defs
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars
import Sheaf.AlgebraicGeometry.ProEtaleToposFunctorialityInverseImage
import Sheaf.AlgebraicGeometry.ProEtale.AffineClosedInverseImageEvaluation
import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyContractibleEvaluationExact
import Sheaf.AlgebraicGeometry.ProEtaleSpecializationCounit
import Sheaf.AlgebraicGeometry.ProEtaleSpecializationUnitComparison
import Sheaf.AlgebraicGeometry.ProEtaleInverseImageTensorComparison
import WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import Sheaf.CategoryTheory.Sites.UnboundedSectionsLocalization
import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
import Sheaf.Paper.LocalizeRingedSiteMorphismGeneral
import Mathlib.CategoryTheory.Functor.Derived.Adjunction
import Sheaf.CategoryTheory.DerivedCategory.CompositionAdjunctionNormalization
import Sheaf.Paper.RingedDerivedSliceLocalization
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Sheaf.CategoryTheory.InternalSectionScalarAdjunction

/-!
# The canonical derived exchange on closed lifted tests

Source: Stacks Project, Tags 09BL and 0D6F, and the unit--counit calculation
(blueprint: lem-sfb-closed-test-derived-exchange-model).

## Main definitions

* `exchange`: the specified derived adjunction mate.
* `testRestriction`: restriction along the actual closed test-fibre map.
* `restrictPush`: the coefficient comparison induced by the ordinary section identity.

## Main statements

* `closed_test_derived_exchange_model`: the two normalized derived isomorphisms.
* `closed_test_test_naturality`: compatibility with admissible test maps.
* `section_comparison_base_change_naturality`: compatibility with localization cubes.
* `derived_restriction_localization`: localization of canonical restriction.
* `closed_test_coefficient_naturality`: compatibility with actual coefficient maps.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.ClosedTestDerivedExchangeModel

/-- Cache the existing monoidal structure, without changing its data.
Source: internal-module convention
(blueprint: lem-sfb-closed-test-derived-exchange-model). -/
instance (priority := 2500) condensedMonoidal :
    MonoidalCategory (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) :=
  inferInstance

/-- Cache the existing pro-etale sheaf monoidal structure, without changing its data.
Source: internal-module convention
(blueprint: lem-sfb-closed-test-derived-exchange-model). -/
instance (priority := 2500) proetaleMonoidal (X : Scheme.{u}) :
    MonoidalCategory (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) :=
  inferInstance

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- Cache the recorded abelian structure on the same internal module category.
Source: internal-module and K-injective convention
(blueprint: lem-sfb-closed-test-derived-exchange-model). -/
instance (priority := 2500) moduleAbelian (X : Scheme.{u}) :
    Abelian (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :=
  inferInstance

/-- Cache additivity of the recorded terminal-object sections functor.
The body uses the existing additive forgetful and evaluation instances.
Source: global sections convention
(blueprint: lem-sfb-closed-test-derived-exchange-model). -/
instance (priority := 2500) moduleSectionsAdditive (X : Scheme.{u}) :
    (condensedModuleSections Λ X).Additive :=
  inferInstance

/-- Exact pullback, from the recorded module inverse image.
Source: Tags 09BL and 0D6F (blueprint: lem-sfb-closed-test-derived-exchange-model). -/
def pull {X Y : Scheme.{u}} (f : X ⟶ Y) :
    DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y)) ⥤
    DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)) :=
  (CondensedRing.upperStar Λ f).mapDerivedCategory

/-- The canonical derived adjunction with exact inverse image.
Source: Tag 09T5 (blueprint: lem-sfb-closed-test-derived-exchange-model). -/
def adj {X Y : Scheme.{u}} (f : X ⟶ Y) :
    pull Λ f ⊣ CondensedRing.moduleObjectDerivedPushforward Λ f :=
  (CondensedRing.upperStarLowerStarAdjunction Λ f).mapDerivedCategoryRightDerivedAdjunction

/-- Composition of exact pullbacks, using the recorded ordinary composition.
Source: Tag 09T5 (blueprint: lem-sfb-closed-test-derived-exchange-model). -/
def pullComp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    pull Λ (f ≫ g) ≅ pull Λ g ⋙ pull Λ f :=
  Functor.mapDerivedCategoryNatIso (CondensedRing.upperStarComp Λ f g) ≪≫
    Functor.mapDerivedCategoryCompIso _ _

/-- The canonical pullback comparison of a commutative square.
Source: Tag 09BL, specified mate (blueprint: lem-sfb-closed-test-derived-exchange-model). -/
def square {X U T Z : Scheme.{u}} {f : X ⟶ U} {s : Z ⟶ U}
    {h : T ⟶ X} {fZ : T ⟶ Z} (w : CommSq h fZ f s) :
    pull Λ s ⋙ pull Λ fZ ≅ pull Λ f ⋙ pull Λ h :=
  (pullComp Λ fZ s).symm ≪≫
    eqToIso (congrArg (fun b : T ⟶ U ↦ pull Λ b) w.w.symm) ≪≫ pullComp Λ h f

/-- The specified exchange, constructed as the adjunction mate.
Source: Tag 09BL, unit--counit calculation
(blueprint: lem-sfb-closed-test-derived-exchange-model). -/
def exchange {X U T Z : Scheme.{u}} {f : X ⟶ U} {s : Z ⟶ U}
    {h : T ⟶ X} {fZ : T ⟶ Z} (w : CommSq h fZ f s) :
    CondensedRing.moduleObjectDerivedPushforward Λ f ⋙ pull Λ s ⟶
      pull Λ h ⋙ CondensedRing.moduleObjectDerivedPushforward Λ fZ :=
  Adjunction.squareExchange (adj Λ f) (adj Λ fZ) (pull Λ s) (pull Λ h) (square Λ w)

/-- Canonical global-section composition before deriving.
Source: Tag 0D6E, sectionwise identity
(blueprint: lem-sfb-closed-test-derived-exchange-model). -/
def pushSectionsIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    CondensedRing.lowerStar Λ f ⋙ condensedModuleSections Λ Y ≅
      condensedModuleSections Λ X :=
  Functor.isoWhiskerLeft (CondensedRing.lowerStar Λ f)
      (Functor.isoWhiskerLeft (Mod.forget (condensedRingObj Λ Y))
        (Sheaf.ΓNatIsoSheafSections (Scheme.ProEt.topology Y) Ab.{u + 1}
          (Scheme.ProEt.isTerminalMkId Y))).symm ≪≫
    Functor.isoWhiskerLeft (Mod.forget (condensedRingObj Λ X))
      (ProEtale.globalSectionsLowerStarIso Ab.{u + 1} f) ≪≫
    Functor.isoWhiskerLeft (Mod.forget (condensedRingObj Λ X))
      (Sheaf.ΓNatIsoSheafSections (Scheme.ProEt.topology X) Ab.{u + 1}
        (Scheme.ProEt.isTerminalMkId X))

/-- K-injective preservation is supplied by the existing exact inverse-image adjunction.
Source: Tag 08BJ (blueprint: lem-sfb-closed-test-derived-exchange-model). -/
instance lowerStarPreservesKInjective {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (CondensedRing.lowerStar Λ f).PreservesKInjectiveComplexes :=
  (CondensedRing.upperStarLowerStarAdjunction Λ f).preservesKInjectiveComplexes

/-- Derived composition for global sections, normalized by the ordinary section identity.
Source: Tag 0D6E (blueprint: lem-sfb-closed-test-derived-exchange-model). -/
def pushDerivedSectionsIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    CondensedRing.moduleObjectDerivedPushforward Λ f ⋙
        (condensedModuleSections Λ Y).rightDerivedFunctor ≅
      (condensedModuleSections Λ X).rightDerivedFunctor :=
  Functor.rightDerivedFunctorCompIso' _ _ (pushSectionsIso Λ f)

/-- Canonical derived restriction: the derived unit, followed by section composition.
Source: Tags 09T5 and 0D6E
(blueprint: lem-sfb-closed-test-derived-exchange-model). -/
def restriction {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (condensedModuleSections Λ Y).rightDerivedFunctor ⟶
      pull Λ f ⋙ (condensedModuleSections Λ X).rightDerivedFunctor :=
  Functor.whiskerRight (adj Λ f).unit
      (condensedModuleSections Λ Y).rightDerivedFunctor ≫
    Functor.whiskerLeft (pull Λ f) (pushDerivedSectionsIso Λ f).hom

/-- Derived sections on the source of b, after the existing exact pullback.
For a pro-etale b this is the canonical localized-site derived sections.
Source: Tag 0D6F (blueprint: lem-sfb-closed-test-derived-exchange-model). -/
def sectionsOver {X W : Scheme.{u}} (b : W ⟶ X) :
    DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)) ⥤ DerivedCategory Ab.{u + 1} :=
  pull Λ b ⋙ (condensedModuleSections Λ W).rightDerivedFunctor

/-- Restriction between two schemes over X, with the canonical pullback composition.
Source: Tags 0D6E--0D6F (blueprint: lem-sfb-closed-test-derived-exchange-model). -/
def restrictionOver {X W W' : Scheme.{u}} (b : W ⟶ X) (a : W' ⟶ W) :
    sectionsOver Λ b ⟶ sectionsOver Λ (a ≫ b) :=
  Functor.whiskerLeft (pull Λ b) (restriction Λ a) ≫
    Functor.whiskerRight (pullComp Λ a b).inv
      (condensedModuleSections Λ W').rightDerivedFunctor

/-- The canonical Leray/base-change section comparison of a commutative square.
It is defined without an invertibility assumption.
Source: Tags 09BL and 0D6E (blueprint: lem-sfb-closed-test-derived-exchange-model). -/
def sectionComparison {X U T W : Scheme.{u}} {f : X ⟶ U} {b : W ⟶ U}
    {h : T ⟶ X} {fW : T ⟶ W} (w : CommSq h fW f b) :
    CondensedRing.moduleObjectDerivedPushforward Λ f ⋙ sectionsOver Λ b ⟶
      sectionsOver Λ h :=
  Functor.whiskerRight (exchange Λ w)
      (condensedModuleSections Λ W).rightDerivedFunctor ≫
    Functor.whiskerLeft (pull Λ h) (pushDerivedSectionsIso Λ fW).hom

/-- Restriction to V from its closed-site lift, along the actual closed inclusion.
The equality uses the geometric pullback statement, not an arbitrary comparison map.
Source: Tag 09BL (2) (blueprint: lem-sfb-closed-test-derived-exchange-model). -/
def closedComparison (A : Type u) [CommRing A] (I : Ideal A)
    (V : (Spec (.of (A ⧸ I))).AffineProEt) :
    sectionsOver Λ ((Scheme.AffineProEt.closedSiteLift A I).obj V).hom ⟶
      pull Λ (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) ⋙
        sectionsOver Λ V.hom :=
  restrictionOver Λ _ (Scheme.AffineProEt.closedSiteLiftInclusion A I V) ≫
    (eqToIso (congrArg (fun b ↦ sectionsOver Λ b)
      ((Scheme.AffineProEt.affine_closed_site_functor_properties A I).2.2.2.2.2.2.2
        V).2.1.w)).hom ≫
    Functor.whiskerRight (pullComp Λ V.hom
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))).hom
      (condensedModuleSections Λ V.left).rightDerivedFunctor

/-- The closed subscheme morphism Spec(A/I) → Spec A.
Source: Tag 09BL (blueprint: lem-sfb-closed-test-derived-exchange-model). -/
abbrev closedMap (A : Type u) [CommRing A] (I : Ideal A) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))

/-- The map from the closed test fibre to its lifted test fibre, by the pullback property.
Source: Tag 09BK (blueprint: lem-sfb-closed-test-derived-exchange-model). -/
def testMap (A : Type u) [CommRing A] (I : Ideal A)
    {X XZ : Scheme.{u}} {f : X ⟶ Spec (.of A)}
    {h : XZ ⟶ X} {fZ : XZ ⟶ Spec (.of (A ⧸ I))}
    (w : CommSq h fZ f (closedMap A I))
    (V : (Spec (.of (A ⧸ I))).AffineProEt) :
    pullback fZ V.hom ⟶ pullback f ((Scheme.AffineProEt.closedSiteLift A I).obj V).hom :=
  pullback.lift (pullback.fst fZ V.hom ≫ h)
    (pullback.snd fZ V.hom ≫ Scheme.AffineProEt.closedSiteLiftInclusion A I V)
    (by
      rw [Category.assoc, w.w, ← Category.assoc, pullback.condition, Category.assoc]
      rw [Category.assoc,
        ((Scheme.AffineProEt.affine_closed_site_functor_properties A I).2.2.2.2.2.2.2
          V).2.1.w])

/-- Restriction on the two actual test fibres, including its canonical target identification.
Source: Tags 09BL and 0D6F (blueprint: lem-sfb-closed-test-derived-exchange-model). -/
def testRestriction (A : Type u) [CommRing A] (I : Ideal A)
    {X XZ : Scheme.{u}} {f : X ⟶ Spec (.of A)}
    {h : XZ ⟶ X} {fZ : XZ ⟶ Spec (.of (A ⧸ I))}
    (w : CommSq h fZ f (closedMap A I))
    (V : (Spec (.of (A ⧸ I))).AffineProEt) :
    sectionsOver Λ (pullback.fst f ((Scheme.AffineProEt.closedSiteLift A I).obj V).hom) ⟶
      pull Λ h ⋙ sectionsOver Λ (pullback.fst fZ V.hom) :=
  restrictionOver Λ _ (testMap A I w V) ≫
    (eqToIso (congrArg (fun b ↦ sectionsOver Λ b)
      (pullback.lift_fst _ _ _))).hom ≫
    Functor.whiskerRight (pullComp Λ (pullback.fst fZ V.hom) h).hom
      (condensedModuleSections Λ (pullback fZ V.hom)).rightDerivedFunctor

/-- The canonical test-section form of the specified exchange.
Source: Tag 09BL, mate definition
(blueprint: lem-sfb-closed-test-derived-exchange-model). -/
def evaluatedExchange (A : Type u) [CommRing A] (I : Ideal A)
    {X XZ : Scheme.{u}} {f : X ⟶ Spec (.of A)}
    {h : XZ ⟶ X} {fZ : XZ ⟶ Spec (.of (A ⧸ I))}
    (w : CommSq h fZ f (closedMap A I))
    (V : (Spec (.of (A ⧸ I))).AffineProEt) :
    CondensedRing.moduleObjectDerivedPushforward Λ f ⋙ pull Λ (closedMap A I) ⋙
        sectionsOver Λ V.hom ⟶
      pull Λ h ⋙ CondensedRing.moduleObjectDerivedPushforward Λ fZ ⋙
        sectionsOver Λ V.hom :=
  Functor.whiskerRight (exchange Λ w) (sectionsOver Λ V.hom)

/-- Restriction between tests with a specified commuting triangle.
Source: Tag 0D6F (blueprint: lem-sfb-closed-test-derived-exchange-model). -/
def sectionsArrow {X W W' : Scheme.{u}} {b : W ⟶ X} {b' : W' ⟶ X}
    (a : W' ⟶ W) (ha : a ≫ b = b') :
    sectionsOver Λ b ⟶ sectionsOver Λ b' :=
  restrictionOver Λ b a ≫ (eqToIso (congrArg (fun q ↦ sectionsOver Λ q) ha)).hom

/-- The induced map of test fibres, given by the actual pullback universal property.
Source: Tag 09BL (blueprint: lem-sfb-closed-test-derived-exchange-model). -/
def fibreMap {X U W W' : Scheme.{u}} (f : X ⟶ U) {b : W ⟶ U} {b' : W' ⟶ U}
    (a : W' ⟶ W) (ha : a ≫ b = b') : pullback f b' ⟶ pullback f b :=
  pullback.lift (pullback.fst f b') (pullback.snd f b' ≫ a)
    (by rw [Category.assoc, ha, pullback.condition])

/-- Test-object naturality of the canonical Leray section comparison.
The commuting triangle is the triangle of the actual affine-site map.
Source: Tag 09BL, natural evaluation, and Tag 0D6F
(blueprint: lem-sfb-closed-test-derived-exchange-model). -/
def TestNaturality {X U W W' : Scheme.{u}} (f : X ⟶ U)
    {b : W ⟶ U} {b' : W' ⟶ U} (a : W' ⟶ W) (ha : a ≫ b = b') : Prop :=
  ∀ K : DerivedCategory.Plus
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)),
    (sectionComparison Λ (IsPullback.of_hasPullback f b).toCommSq).app K.obj ≫
        (sectionsArrow Λ (fibreMap f a ha) (pullback.lift_fst _ _ _)).app K.obj =
      (sectionsArrow Λ a ha).app
          ((CondensedRing.moduleObjectDerivedPushforward Λ f).obj K.obj) ≫
        (sectionComparison Λ (IsPullback.of_hasPullback f b').toCommSq).app K.obj

/-- The two section comparisons and the closed evaluation comparison respect every map
of admissible affine tests, with the maps induced by the specified closed-site functor.
Source: Tag 09BL (2), natural evaluation
(blueprint: lem-sfb-closed-test-derived-exchange-model).

Proof (step 8): the ordinary unit-section isomorphism commutes with affine-site maps.
The chain-section identity, the K-injective comparison units and the derived composition
constraints commute with these restrictions. Thus the same equality descends to D(Ab).
The defining normalizations of eLeft and eRight then give their test naturality. -/
theorem closed_test_test_naturality
    (A : Type u) [CommRing A] (I : Ideal A)
    {X XZ : Scheme.{u}} [IsAffine X] (f : X ⟶ Spec (.of A))
    (fZ : XZ ⟶ Spec (.of (A ⧸ I)))
    (V V' : (Spec (.of (A ⧸ I))).AffineProEt) (r : V' ⟶ V)
    [IsWContractibleRing Γ(V.left, ⊤)] [IsWContractibleRing Γ(V'.left, ⊤)]
    [IsWContractibleRing Γ(((Scheme.AffineProEt.closedSiteLift A I).obj V).left, ⊤)]
    [IsWContractibleRing Γ(((Scheme.AffineProEt.closedSiteLift A I).obj V').left, ⊤)] :
    TestNaturality Λ f ((Scheme.AffineProEt.closedSiteLift A I).map r).left
        (MorphismProperty.Over.w ((Scheme.AffineProEt.closedSiteLift A I).map r)) ∧
      TestNaturality Λ fZ r.left (MorphismProperty.Over.w r) ∧
      (∀ K : DerivedCategory.Plus
          (Mod (Sheaf (Scheme.ProEt.topology (Spec (.of A))) Ab.{u + 1})
            (condensedRingObj Λ (Spec (.of A)))),
        (closedComparison Λ A I V).app K.obj ≫
            (sectionsArrow Λ r.left (MorphismProperty.Over.w r)).app
              ((pull Λ (closedMap A I)).obj K.obj) =
          (sectionsArrow Λ ((Scheme.AffineProEt.closedSiteLift A I).map r).left
              (MorphismProperty.Over.w ((Scheme.AffineProEt.closedSiteLift A I).map r))).app
                K.obj ≫ (closedComparison Λ A I V').app K.obj) := by
  sorry

/-- Canonical section comparison commutes with pro-etale base change and isomorphisms
of squares. All maps of the cube, including its test-fibre face, are retained.
Source: Tags 0D6E--0D6F and the statement's localization clause
(blueprint: lem-sfb-closed-test-derived-exchange-model).

Proof (step 9): Localized direct images are given by the same fibre-product section
formula. Localization preserves units and counits, and exact pullback composition is
coherent. Both composites therefore give the same ordinary restriction on a K-injective
representative; the canonical derived composition units descend that equality. This
includes isomorphisms, since their base morphisms are pro-etale. -/
theorem section_comparison_base_change_naturality
    {X U T W X' U' T' W' : Scheme.{u}}
    {f : X ⟶ U} {b : W ⟶ U} {h : T ⟶ X} {fW : T ⟶ W}
    {f' : X' ⟶ U'} {b' : W' ⟶ U'} {h' : T' ⟶ X'} {fW' : T' ⟶ W'}
    (a : X' ⟶ X) (v : U' ⟶ U) (t : T' ⟶ T) (k : W' ⟶ W)
    [WeaklyEtale v] [WeaklyEtale b] [WeaklyEtale b']
    (w : IsPullback h fW f b) (w' : IsPullback h' fW' f' b')
    (wf : IsPullback a f' f v) (wb : IsPullback k b' b v)
    (wh : IsPullback t h' h a) (_wW : IsPullback t fW' fW k)
    (K : DerivedCategory.Plus
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))) :
    (sectionComparison Λ w.toCommSq).app K.obj ≫
        (sectionsArrow Λ t wh.w).app K.obj ≫
        (condensedModuleSections Λ T').rightDerivedFunctor.map
          ((pullComp Λ h' a).hom.app K.obj) =
      (sectionsArrow Λ k wb.w).app
          ((CondensedRing.moduleObjectDerivedPushforward Λ f).obj K.obj) ≫
        (condensedModuleSections Λ W').rightDerivedFunctor.map
          ((pullComp Λ b' v).hom.app
            ((CondensedRing.moduleObjectDerivedPushforward Λ f).obj K.obj)) ≫
        (sectionsOver Λ b').map ((exchange Λ wf.toCommSq).app K.obj) ≫
        (sectionComparison Λ w'.toCommSq).app ((pull Λ a).obj K.obj) := by
  sorry

/-- The derived restriction appearing in the closed-test normalization commutes with
pro-etale localization, using the specified composition constraints.
Source: Tags 09T5 and 0D6E--0D6F
(blueprint: lem-sfb-closed-test-derived-exchange-model).

Proof (steps 7 and 9): Composition of the two adjunction units is the unit of the
composite adjunction. The section comparison is normalized by the ordinary identity.
Apply this twice to the two equal composites in the localization square. Pullback
composition identifies their coefficients and gives precisely the displayed equation. -/
theorem derived_restriction_localization
    {T W T' W' : Scheme.{u}} (a : W ⟶ T) (a' : W' ⟶ T')
    (t : T' ⟶ T) (k : W' ⟶ W) [WeaklyEtale t]
    (w : IsPullback k a' a t)
    (K : DerivedCategory.Plus
      (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T))) :
    (restriction Λ a).app K.obj ≫
        (restriction Λ k).app ((pull Λ a).obj K.obj) ≫
        (condensedModuleSections Λ W').rightDerivedFunctor.map
          ((pullComp Λ k a).inv.app K.obj) ≫
        (condensedModuleSections Λ W').rightDerivedFunctor.map
          ((eqToIso (congrArg (fun q : W' ⟶ T ↦ pull Λ q) w.w)).hom.app K.obj) =
      (restriction Λ t).app K.obj ≫
        (restriction Λ a').app ((pull Λ t).obj K.obj) ≫
        (condensedModuleSections Λ W').rightDerivedFunctor.map
          ((pullComp Λ a' t).inv.app K.obj) := by
  sorry

section Coefficients

variable {Λ} {Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ'] [IsCommMonObj Λ'] (c : Λ ⟶ Λ') [IsMonHom c]

/-- The existing exact restriction of scalars on ordinary unbounded derived categories.
Source: scalar clause and Tag 0D6E
(blueprint: lem-sfb-closed-test-derived-exchange-model). -/
def restrict (X : Scheme.{u}) :
    DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ' X)) ⥤
    DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)) :=
  (Mod.comap (coefficientMap c X)).mapDerivedCategory

/-- The canonical right-derived direct-image coefficient comparison. Its direction is fixed
by the ordinary section identity; no preservation of injectives by restriction is assumed.
Source: the statement's coefficient clause and proof step 10
(blueprint: lem-sfb-closed-test-derived-exchange-model). -/
def restrictPush {X Y : Scheme.{u}} (f : X ⟶ Y) :
    CondensedRing.moduleObjectDerivedPushforward Λ' f ⋙ restrict c Y ⟶
      restrict c X ⋙ CondensedRing.moduleObjectDerivedPushforward Λ f :=
  (Functor.rightDerivedFunctorCompMapDerivedCategoryIso
      (CondensedRing.lowerStar Λ' f) (Mod.comap (coefficientMap c Y))).inv ≫
    Functor.rightDerivedPullback (Mod.comap (coefficientMap c X))
      (CondensedRing.comapLowerStarIso c f).hom

/-- The derived coefficient map on global sections, induced by the literal underlying
section identity and the universal right-derived unit.
Source: coefficient clause, proof step 10
(blueprint: lem-sfb-closed-test-derived-exchange-model). -/
def restrictSections (X : Scheme.{u}) :
    (condensedModuleSections Λ' X).rightDerivedFunctor ⟶
      restrict c X ⋙ (condensedModuleSections Λ X).rightDerivedFunctor :=
  Functor.rightDerivedPullback (Mod.comap (coefficientMap c X)) (𝟙 _)

/-- Coefficient restriction on localized sections uses the existing exact pullback comparison.
Source: coefficient clause and Tag 0D6F
(blueprint: lem-sfb-closed-test-derived-exchange-model). -/
def restrictSectionsOver {X W : Scheme.{u}} (b : W ⟶ X) :
    sectionsOver Λ' b ⟶ restrict c X ⋙ sectionsOver Λ b :=
  Functor.whiskerLeft (pull Λ' b) (restrictSections c W) ≫
    Functor.whiskerRight (CondensedRing.derivedComapUpperStarIso c b).hom
      (condensedModuleSections Λ W).rightDerivedFunctor

/-- The actual ordinary extension unit in degree zero, with exact restriction of scalars.
Source: the final sentence of the item, x ↦ 1 tensor x
(blueprint: lem-sfb-closed-test-derived-exchange-model). -/
def scalarUnit (X : Scheme.{u})
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    (DerivedCategory.singleFunctor _ 0).obj M ⟶
      (restrict c X).obj ((DerivedCategory.singleFunctor _ 0).obj
        ((Mod.extendScalars (coefficientMap c X)).obj M)) :=
  (DerivedCategory.singleFunctor _ 0).map
      ((Mod.extendRestrictAdjunction (coefficientMap c X)).unit.app M) ≫
    ((Mod.comap (coefficientMap c X)).mapDerivedCategorySingleFunctor 0).inv.app
      ((Mod.extendScalars (coefficientMap c X)).obj M)

/-- Commutativity of the section-comparison square for the actual coefficient map.
Source: coefficient clause, proof steps 10--11
(blueprint: lem-sfb-closed-test-derived-exchange-model). -/
def CoefficientSectionComparison {X U T W : Scheme.{u}} {f : X ⟶ U} {b : W ⟶ U}
    {h : T ⟶ X} {fW : T ⟶ W} (w : CommSq h fW f b)
    (N : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ' X))) : Prop :=
  (restrictSectionsOver c b).app
        ((CondensedRing.moduleObjectDerivedPushforward Λ' f).obj N) ≫
      (sectionsOver Λ b).map ((restrictPush c f).app N) ≫
      (sectionComparison Λ w).app ((restrict c X).obj N) =
    (sectionComparison Λ' w).app N ≫ (restrictSectionsOver c h).app N

/-- Commutativity of the closed-test unit square under restriction of scalars.
Source: coefficient clause, proof step 10
(blueprint: lem-sfb-closed-test-derived-exchange-model). -/
def CoefficientClosedComparison (A : Type u) [CommRing A] (I : Ideal A)
    (V : (Spec (.of (A ⧸ I))).AffineProEt)
    (N : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology (Spec (.of A))) Ab.{u + 1})
      (condensedRingObj Λ' (Spec (.of A))))) : Prop :=
  (closedComparison Λ' A I V).app N ≫
      (restrictSectionsOver c V.hom).app ((pull Λ' (closedMap A I)).obj N) ≫
      (sectionsOver Λ V.hom).map
        ((CondensedRing.derivedComapUpperStarIso c (closedMap A I)).hom.app N) =
    (restrictSectionsOver c ((Scheme.AffineProEt.closedSiteLift A I).obj V).hom).app N ≫
      (closedComparison Λ A I V).app ((restrict c (Spec (.of A))).obj N)

/-- Commutativity of derived restriction and the actual coefficient section map.
Source: coefficient clause and Tag 0D6F
(blueprint: lem-sfb-closed-test-derived-exchange-model). -/
def CoefficientRestriction {X W W' : Scheme.{u}} (b : W ⟶ X) (a : W' ⟶ W)
    (N : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ' X))) : Prop :=
  (restrictionOver Λ' b a).app N ≫ (restrictSectionsOver c (a ≫ b)).app N =
    (restrictSectionsOver c b).app N ≫
      (restrictionOver Λ b a).app ((restrict c X).obj N)

/-- Every coefficient comparison square commutes, including the square of any supplied
module morphism K → Res N. There is no scalar/direct-image invertibility assumption.
Source: coefficient clause and proof steps 10--11
(blueprint: lem-sfb-closed-test-derived-exchange-model).

Proof: On underlying section complexes the ordinary scalar comparison is the identity.
Use the universal right-derived units to define its direct-image comparison, without
assuming restriction preserves K-injectives. Units, counits, pullback composition and
restriction commute with this identity. Hence the two section-comparison squares and
closed-unit square commute, as does derived restriction. The remaining equation is the
naturality square at the actual supplied module map. For a degree-zero module apply it
to scalarUnit, which is precisely the ordinary extension unit, not derived tensor. -/
theorem closed_test_coefficient_naturality
    (A : Type u) [CommRing A] (I : Ideal A)
    {X XZ : Scheme.{u}} [IsAffine X] (f : X ⟶ Spec (.of A))
    (h : XZ ⟶ X) (fZ : XZ ⟶ Spec (.of (A ⧸ I)))
    (w : IsPullback h fZ f (closedMap A I))
    (V : (Spec (.of (A ⧸ I))).AffineProEt)
    [IsWContractibleRing Γ(V.left, ⊤)]
    [IsWContractibleRing Γ(((Scheme.AffineProEt.closedSiteLift A I).obj V).left, ⊤)]
    (K : DerivedCategory.Plus
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))
    (N : DerivedCategory.Plus
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ' X)))
    (φ : K.obj ⟶ (restrict c X).obj N.obj) :
    CoefficientSectionComparison c
        (IsPullback.of_hasPullback f
          ((Scheme.AffineProEt.closedSiteLift A I).obj V).hom).toCommSq N.obj ∧
      CoefficientSectionComparison c (IsPullback.of_hasPullback fZ V.hom).toCommSq
        ((pull Λ' h).obj N.obj) ∧
      CoefficientClosedComparison c A I V
        ((CondensedRing.moduleObjectDerivedPushforward Λ' f).obj N.obj) ∧
      CoefficientRestriction c
        (pullback.fst f ((Scheme.AffineProEt.closedSiteLift A I).obj V).hom)
        (testMap A I w.toCommSq V) N.obj ∧
      (CondensedRing.moduleObjectDerivedPushforward Λ f ⋙ pull Λ (closedMap A I) ⋙
          sectionsOver Λ V.hom).map φ ≫
          (evaluatedExchange Λ A I w.toCommSq V).app ((restrict c X).obj N.obj) =
        (evaluatedExchange Λ A I w.toCommSq V).app K.obj ≫
          (pull Λ h ⋙ CondensedRing.moduleObjectDerivedPushforward Λ fZ ⋙
            sectionsOver Λ V.hom).map φ := by
  sorry

end Coefficients

/-- The derived comparison isomorphisms, with their unit normalization and mate equation.
Source: Stacks Project, Tags 09BL (1)--(2), 0D6E--0D6F
(blueprint: lem-sfb-closed-test-derived-exchange-model).

Proof: (1) Transport internal modules through the fixed section-ring equivalence,
which preserves underlying abelian sheaves, sections, exactness and K-injectivity
[def-weil-pbc-internal-abelian-sheaf-module-equivalence].
The coefficient inverse-image maps are isomorphisms, hence every pullback is exact
[sk-def-sfb-module-pushforward-pullback, lem-zl-condensed-lisse-proetale-locality].
(2) The two geometric w-contractible tests have exact evaluation on the full and
basis sites. The closed-site counit and unit-comparison theorems identify the actual
inverse-image unit section with the closed-evaluation isomorphism.
(3) Choose a K-injective I representing K. The exact left adjoint of f_* makes f_*I
K-injective; exact test evaluation and derived section localization identify the source
with Q(I(T)). (4) Resolve h*I by a K-injective J; the same argument identifies the target
with Q(J(T0)). Pullback composition identifies its coefficients with a*(K|T).
(5) On ordinary modules the square comparison followed by the counit sends the unit
section of x to the inverse-image section of x. The triangle identity cancels the
inserted unit and counit. (6) Apply this calculation degreewise to I and then to I → J.
Transposition under the normalized derived adjunction gives the specified exchange.
(7) The resulting I(T) → J(T0) is the derived unit for a followed by the canonical
section composition, which is the degreewise section identity on a K-injective target.
(8) K-injective Hom computation makes this independent of resolutions and natural in K
[lem-weil-pbc-kinjective-hom-derived].
(9) The same units, restrictions and composition constraints commute with test maps,
isomorphisms of squares and pro-etale localizations. (10) Restriction of scalars is
exact and its underlying section maps are identities; the universal derived comparison
has its natural direction and is not assumed invertible. (11) Apply this to the actual
map K → Res N and, in degree zero, to the ordinary extension unit x ↦ 1 tensor x. -/
theorem closed_test_derived_exchange_model
    (A : Type u) [CommRing A] (I : Ideal A)
    {X XZ : Scheme.{u}} [IsAffine X] (f : X ⟶ Spec (.of A))
    (h : XZ ⟶ X) (fZ : XZ ⟶ Spec (.of (A ⧸ I)))
    (w : IsPullback h fZ f (closedMap A I))
    (V : (Spec (.of (A ⧸ I))).AffineProEt)
    [IsWContractibleRing Γ(V.left, ⊤)]
    [IsWContractibleRing Γ(((Scheme.AffineProEt.closedSiteLift A I).obj V).left, ⊤)] :
    ∃ eLeft :
        DerivedCategory.Plus.ι ⋙ CondensedRing.moduleObjectDerivedPushforward Λ f ⋙
            pull Λ (closedMap A I) ⋙ sectionsOver Λ V.hom ≅
          DerivedCategory.Plus.ι ⋙ sectionsOver Λ
            (pullback.fst f ((Scheme.AffineProEt.closedSiteLift A I).obj V).hom),
      ∃ eRight :
        DerivedCategory.Plus.ι ⋙ pull Λ h ⋙
            CondensedRing.moduleObjectDerivedPushforward Λ fZ ⋙ sectionsOver Λ V.hom ≅
          DerivedCategory.Plus.ι ⋙ pull Λ h ⋙
            sectionsOver Λ (pullback.fst fZ V.hom),
        (∀ K : DerivedCategory.Plus
            (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)),
          IsIso ((closedComparison Λ A I V).app
            ((CondensedRing.moduleObjectDerivedPushforward Λ f).obj K.obj)) ∧
          (closedComparison Λ A I V).app
              ((CondensedRing.moduleObjectDerivedPushforward Λ f).obj K.obj) ≫
                eLeft.hom.app K =
            (sectionComparison Λ (IsPullback.of_hasPullback f
              ((Scheme.AffineProEt.closedSiteLift A I).obj V).hom).toCommSq).app K.obj) ∧
        eRight.hom = Functor.whiskerLeft (DerivedCategory.Plus.ι ⋙ pull Λ h)
          (sectionComparison Λ (IsPullback.of_hasPullback fZ V.hom).toCommSq) ∧
        Functor.whiskerLeft DerivedCategory.Plus.ι
            (evaluatedExchange Λ A I w.toCommSq V) ≫ eRight.hom =
          eLeft.hom ≫ Functor.whiskerLeft DerivedCategory.Plus.ι
            (testRestriction Λ A I w.toCommSq V) := by
  sorry

end AlgebraicGeometry.ProEtale.ClosedTestDerivedExchangeModel
