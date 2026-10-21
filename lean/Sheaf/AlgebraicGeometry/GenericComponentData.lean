/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N1
-/
module

public import Sheaf.AlgebraicGeometry.AffineComponentSiteProjection
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Mathlib.Algebra.Homology.DerivedCategory.Basic

/-!
# Canonical affine component data and scalar compatibility

The functor and geometric morphism are extracted from the geometric characterization
in Bhatt--Scholze Lemmas 2.2.8 and 4.2.13(1). The final predicate records the scalar
comparison of HRS following diagram (4.4).
(blueprint: def-zl-generic-component-data).
-/

@[expose] public section

set_option autoImplicit false

universe u wR wS wV wCJ wCK

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.ProEt

/-- The affine component functor characterized by the locally ringed space
`|T| ×_π₀(T) E`, using the full construction theorem, not an arbitrary functor.
The characterization determines it up to the unique natural isomorphism over T
and over E, which is the equality used for the ensuing sheaf morphisms.
Source: Bhatt--Scholze Lemma 2.2.8 and 4.2.13(1)
(blueprint: def-zl-generic-component-data). -/
noncomputable def genericComponentFunctor (T : Scheme.{u}) [IsAffine T] :
    Over (componentProfinite T) ⥤ T.ProEt :=
  (affine_component_site_projection T).choose

/-- Coordinates of the canonical component functor, retained from its geometric
characterization. Source: Bhatt--Scholze Lemma 2.2.8
(blueprint: def-zl-generic-component-data). -/
noncomputable def genericComponentCoordinates (T : Scheme.{u}) [IsAffine T] :
    ∀ E : Over (componentProfinite T),
      C(((genericComponentFunctor T).obj E).left, E.left) :=
  (affine_component_site_projection T).choose_spec.choose

/-- Continuity of the chosen, geometrically characterized component functor.
Source: Bhatt--Scholze Lemma 4.2.13(1)
(blueprint: def-zl-generic-component-data). -/
noncomputable instance genericComponentContinuous (T : Scheme.{u}) [IsAffine T] :
    (genericComponentFunctor T).IsContinuous
      ((coherentTopology Profinite.{u}).over (componentProfinite T)) (topology T) :=
  ((affine_component_site_projection T).choose_spec.choose_spec.2.2.2.2).choose

/-- The canonical component morphism on sets, extracted from the evaluation of the
same functor. Its direct image is restriction along `genericComponentFunctor T`.
Source: Bhatt--Scholze Lemma 4.2.13(1)
(blueprint: def-zl-generic-component-data). -/
noncomputable def genericComponentProjection (T : Scheme.{u}) [IsAffine T] :
    GeometricMorphism (Sheaf (topology T) (Type (u + 1)))
      (Sheaf ((coherentTopology Profinite.{u}).over (componentProfinite T))
        (Type (u + 1))) :=
  ((affine_component_site_projection T).choose_spec.choose_spec.2.2.2.2).choose_spec.1.choose

/-- The ring-valued inverse image induced by the very same component functor.
Its right adjoint is restriction along that functor, so its operations and
adjunction unit are those of the canonical algebraic lift.
Source: Bhatt--Scholze Lemma 4.2.13(1) and HRS Theorem 4.13, diagram (4.4)
(blueprint: def-zl-generic-component-data). -/
noncomputable abbrev genericComponentRingPush (T : Scheme.{u}) [IsAffine T] :=
  (genericComponentFunctor T).sheafPushforwardContinuous RingCat.{u + 1}
    ((coherentTopology Profinite.{u}).over (componentProfinite T)) (topology T)

/-- The scalar-extension compatibility, characterized without any choice of a resolution.
For a ring map from a discrete ring to global coefficients, extension of constants is
left adjoint to global sections with that scalar action. Its unbounded left derived
functor is characterized by the displayed localization counit. The assertion says that
these actual scalar extensions commute with the specified component-derived equivalence.
Source: HRS Theorem 4.13, proof after (4.4)
(blueprint: def-zl-generic-component-data). -/
def GenericComponentScalarCompatibility
    {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (A : Sheaf J RingCat.{u + 1}) (B : Sheaf K RingCat.{u + 1})
    (c : C) (d : D) (e : A.obj.obj (op c) ≅ B.obj.obj (op d))
    [HasDerivedCategory.{wS} (ringedSiteModules.{u + 1} A)]
    [HasDerivedCategory.{wV} (ringedSiteModules.{u + 1} B)]
    (E : DerivedCategory (ringedSiteModules.{u + 1} A) ≌
      DerivedCategory (ringedSiteModules.{u + 1} B)) : Prop :=
  (∀ (R : Type (u + 1)) [Ring R]
    [HasDerivedCategory.{wR} (ModuleCat.{u + 1} R)]
    (a : R →+* A.obj.obj (op c))
    (FS : ModuleCat.{u + 1} R ⥤ ringedSiteModules.{u + 1} A)
    (FV : ModuleCat.{u + 1} R ⥤ ringedSiteModules.{u + 1} B)
    [FS.Additive] [FV.Additive],
    Nonempty (FS ⊣ SheafOfModules.evaluation A (op c) ⋙ ModuleCat.restrictScalars a) →
    Nonempty (FV ⊣ SheafOfModules.evaluation B (op d) ⋙
      ModuleCat.restrictScalars (e.hom.hom.comp a)) →
    ∀ (LS : DerivedCategory (ModuleCat.{u + 1} R) ⥤
        DerivedCategory (ringedSiteModules.{u + 1} A))
      (LV : DerivedCategory (ModuleCat.{u + 1} R) ⥤
        DerivedCategory (ringedSiteModules.{u + 1} B))
      (εS : DerivedCategory.Qh ⋙ LS ⟶
        FS.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
      (εV : DerivedCategory.Qh ⋙ LV ⟶
        FV.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh),
      LS.IsLeftDerivedFunctor εS
        (HomotopyCategory.quasiIso (ModuleCat.{u + 1} R) (ComplexShape.up ℤ)) →
      LV.IsLeftDerivedFunctor εV
        (HomotopyCategory.quasiIso (ModuleCat.{u + 1} R) (ComplexShape.up ℤ)) →
      Nonempty (LS ⋙ E.functor ≅ LV)) ∧
  (∀ (R : Type (u + 1)) [CommRing R]
    [HasDerivedCategory.{wR} (ModuleCat.{u + 1} R)]
    [HasDerivedCategory.{wCJ} (realizationModules J R)]
    [HasDerivedCategory.{wCK} (realizationModules K R)]
    (aS : (sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      (realizationRing J R) ⟶ A)
    (aV : (sheafCompose K (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      (realizationRing K R) ⟶ B),
    (∀ r : R,
      e.hom.hom ((aS.hom.app (op c)).hom ((realizationRingUnit J R).app (op c) r)) =
        (aV.hom.app (op d)).hom ((realizationRingUnit K R).app (op d) r)) →
    ∀ (FS : realizationModules J R ⥤ ringedSiteModules.{u + 1} A)
      (FV : realizationModules K R ⥤ ringedSiteModules.{u + 1} B)
      [FS.Additive] [FV.Additive],
    Nonempty (FS ⊣ SheafOfModules.restrictScalars aS) →
    Nonempty (FV ⊣ SheafOfModules.restrictScalars aV) →
    ∀ (LS : DerivedCategory (realizationModules J R) ⥤
        DerivedCategory (ringedSiteModules.{u + 1} A))
      (LV : DerivedCategory (realizationModules K R) ⥤
        DerivedCategory (ringedSiteModules.{u + 1} B))
      (εS : DerivedCategory.Qh ⋙ LS ⟶
        FS.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
      (εV : DerivedCategory.Qh ⋙ LV ⟶
        FV.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh),
    LS.IsLeftDerivedFunctor εS
      (HomotopyCategory.quasiIso (realizationModules J R) (ComplexShape.up ℤ)) →
    LV.IsLeftDerivedFunctor εV
      (HomotopyCategory.quasiIso (realizationModules K R) (ComplexShape.up ℤ)) →
    Nonempty (commutativeSiteDerivedConstantModuleFunctor J R ⋙ LS ⋙ E.functor ≅
      commutativeSiteDerivedConstantModuleFunctor K R ⋙ LV))

/-- Constant-ring module transport. Source: HRS, proof following (4.4)
(blueprint: def-zl-generic-component-data). -/
def GenericComponentConstantScalarCompatibility
    {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (A : Sheaf J RingCat.{u + 1}) (B : Sheaf K RingCat.{u + 1})
    (c : C) (d : D) (e : A.obj.obj (op c) ≅ B.obj.obj (op d))
    (E : ringedSiteModules.{u + 1} A ≌ ringedSiteModules.{u + 1} B) : Prop :=
  ∀ (R : Type (u + 1)) [CommRing R],
    ∃ ER : realizationModules J R ≌ realizationModules K R,
    ∃ (_ : ER.functor.Additive),
    Nonempty (commutativeSiteConstantModuleFunctor J R ⋙ ER.functor ≅
      commutativeSiteConstantModuleFunctor K R) ∧
    ∀ (aS : (sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (realizationRing J R) ⟶ A)
      (aV : (sheafCompose K (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (realizationRing K R) ⟶ B),
    (∀ r : R,
      e.hom.hom ((aS.hom.app (op c)).hom ((realizationRingUnit J R).app (op c) r)) =
        (aV.hom.app (op d)).hom ((realizationRingUnit K R).app (op d) r)) →
    ∀ (FS : realizationModules J R ⥤ ringedSiteModules.{u + 1} A)
      (FV : realizationModules K R ⥤ ringedSiteModules.{u + 1} B)
      [FS.Additive] [FV.Additive],
    Nonempty (FS ⊣ SheafOfModules.restrictScalars aS) →
    Nonempty (FV ⊣ SheafOfModules.restrictScalars aV) →
    Nonempty (FS ⋙ E.functor ≅ ER.functor ⋙ FV)

/-- Ordinary scalar comparisons, including the equivalence on the constant-ring
module categories. Source: HRS, proof following (4.4)
(blueprint: def-zl-generic-component-data). -/
def GenericComponentOrdinaryScalarCompatibility
    {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (A : Sheaf J RingCat.{u + 1}) (B : Sheaf K RingCat.{u + 1})
    (c : C) (d : D) (e : A.obj.obj (op c) ≅ B.obj.obj (op d))
    (E : ringedSiteModules.{u + 1} A ≌ ringedSiteModules.{u + 1} B) : Prop :=
  (∀ (R : Type (u + 1)) [Ring R] (a : R →+* A.obj.obj (op c))
    (FS : ModuleCat.{u + 1} R ⥤ ringedSiteModules.{u + 1} A)
    (FV : ModuleCat.{u + 1} R ⥤ ringedSiteModules.{u + 1} B)
    [FS.Additive] [FV.Additive],
    Nonempty (FS ⊣ SheafOfModules.evaluation A (op c) ⋙ ModuleCat.restrictScalars a) →
    Nonempty (FV ⊣ SheafOfModules.evaluation B (op d) ⋙
      ModuleCat.restrictScalars (e.hom.hom.comp a)) →
    Nonempty (FS ⋙ E.functor ≅ FV)) ∧
  GenericComponentConstantScalarCompatibility A B c d e E


end AlgebraicGeometry.Scheme.ProEt
