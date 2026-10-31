/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PullbackIdentitiesScalarExtension
import WeilConjectures.AlgebraicGeometry.IntegralInverseImageComparisonComposition
import WeilConjectures.AlgebraicGeometry.IntegralIdentityCompositorSections
import WeilConjectures.AlgebraicGeometry.NormalizedIntegralGeometricCoherence
import WeilConjectures.AlgebraicGeometry.IsomorphismComparisonNatural
import WeilConjectures.CategoryTheory.ExactDerivedTransformationPasting

/-!
# Integral inverse cancellation after precomposition

The normalized ordinary unit is checked on sections. Composition compatibility and
naturality then force kappa to respect the completed unit, giving the inverse
cancellation identity without another normalization assumption.

Source: the Weil-structures paragraph of the open-closed triangle proof; Stacks
Tags 03D6, 015F and 04VG.
(blueprint: lem-sf-integral-automorphism-cancellation-precomposition)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option linter.style.haveILetI false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale
namespace WeilConjectures

set_option allowUnsafeReducibility true in
attribute [local irreducible] integralDerivedPullback integralComparisonComposition
  integralComparisonUnit inverseImagePullbackComparisonDerived pullbackIdentityEpsilon
  HasDerivedCategory.standard


attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective in
private theorem identityConstant (X : Scheme.{u}) (R : CommRingCat.{u + 1}) :
    isoSectionwiseConstantMap.{u, u} (𝟙 X) R =
      (Functor.sheafPushforwardContinuousId'
        (MorphismProperty.Over.mapId (P := @WeaklyEtale) ⊤ X (𝟙 X) rfl)
        RingCat.{u + 1} (ProEt.topology X)).hom.app
          ((sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
            ((constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).obj R)) := by
  apply (isoSectionwiseConstantMap_existsUnique.{u, u} (𝟙 X) R).unique
  · exact (isoSectionwiseConstantMap_existsUnique.{u, u} (𝟙 X) R).exists.choose_spec
  · intro U x
    exact (congrArg (fun f ↦ f x)
      ((toSheafify (ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj R)).naturality
        ((MorphismProperty.Over.mapId (P := @WeaklyEtale) ⊤ X (𝟙 X) rfl).inv.app U).op)).symm

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective in
private theorem identityCoefficient (X : Scheme.{u}) :
    inverseImageCompletedCoefficientMap l E (𝟙 X) =
      (Functor.sheafPushforwardContinuousId'
        (MorphismProperty.Over.mapId (P := @WeaklyEtale) ⊤ X (𝟙 X) rfl)
        RingCat.{u + 1} (ProEt.topology X)).hom.app
          (completedIntegralCoefficientSheafUnrestricted l E X) := by
  let t := (Functor.sheafPushforwardContinuousId'
    (MorphismProperty.Over.mapId (P := @WeaklyEtale) ⊤ X (𝟙 X) rfl)
    RingCat.{u + 1} (ProEt.topology X)).hom
  apply limit.hom_ext
  intro n
  rw [inverseImageCompletedCoefficientMap, limit.lift_π]
  dsimp only [inverseImageCompletedCoefficientComponent]
  change _ ≫ isoSectionwiseConstantMap.{u, u} (𝟙 X) _ = _
  rw [identityConstant]
  exact t.naturality (limit.π (integralCoefficientSheafSystem l E X) n)

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective in
private def moduleIdentity (X : Scheme.{u}) :
    inverseImageIntegralModules l E (𝟙 X) ≅ 𝟭 (integralTowerModules l E X) := by
  let d := MorphismProperty.Over.mapId (P := @WeaklyEtale) ⊤ X (𝟙 X) rfl
  let R := completedIntegralCoefficientSheafUnrestricted l E X
  let e := (Functor.sheafPushforwardContinuousId' d RingCat.{u + 1}
    (ProEt.topology X)).app R
  have hi : inv (inverseImageCompletedCoefficientMap l E (𝟙 X)) = e.inv := by
    apply IsIso.inv_eq_of_hom_inv_id
    rw [identityCoefficient]
    exact e.hom_inv_id
  exact (SheafOfModules.pushforwardCongr₂
    (J := ProEt.topology X) (K := ProEt.topology X) (S := R) (T := R)
    (F := proEtaleIsoPostcompose (𝟙 X)) (G := 𝟭 X.ProEt)
    (φ := 𝟙 R) d (by
      change 𝟙 R ≫ e.inv = inv (inverseImageCompletedCoefficientMap l E (𝟙 X))
      simpa only [Category.id_comp] using hi.symm)).symm ≪≫
    SheafOfModules.pushforwardId R

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective in
private theorem moduleIdentity_apply (X : Scheme.{u}) (M : integralTowerModules l E X)
    (U : X.ProEt)
    (x : ((inverseImageIntegralModules l E (𝟙 X)).obj M).val.obj (op U)) :
    ((moduleIdentity l E X).hom.app M).val.app (op U) x =
      M.val.map ((MorphismProperty.Over.mapId (P := @WeaklyEtale) ⊤ X (𝟙 X)
        rfl).inv.app U).op x := by
  rfl

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective in
private def derivedIdentity (X : Scheme.{u}) :
    inverseImageIntegralDerived l E (𝟙 X) ≅
      𝟭 (DerivedCategory (integralTowerModules l E X)) :=
  Functor.mapDerivedCategoryNatIso (moduleIdentity l E X) ≪≫
    Functor.mapDerivedCategoryIdIso _

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective in
private def moduleTransport (X : Scheme.{u}) {f g : X ⟶ X}
    [IsIso f] [IsIso g] (w : f = g) :
    inverseImageIntegralModules l E f ≅ inverseImageIntegralModules l E g := by
  subst g
  exact Iso.refl _

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective in
private def derivedTransport (X : Scheme.{u}) {f g : X ⟶ X}
    [IsIso f] [IsIso g] (w : f = g) :
    inverseImageIntegralDerived l E f ≅ inverseImageIntegralDerived l E g := by
  subst g
  exact Iso.refl _

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective in
private theorem moduleReturn_apply (X : Scheme.{u}) (f : X ⟶ X) [IsIso f]
    (w : f = 𝟙 X) (M : integralTowerModules l E X) (U : X.ProEt)
    (x : M.val.obj (op ((proEtaleIsoPostcompose f).obj U))) :
    (((moduleTransport l E X w ≪≫
      moduleIdentity l E X).hom.app M).val.app (op U)) x =
        M.val.map ((MorphismProperty.Over.mapId (P := @WeaklyEtale) ⊤ X f w).inv.app U).op x := by
  subst f
  simpa only [moduleTransport, Iso.refl_trans] using
    moduleIdentity_apply l E X M U x

set_option allowUnsafeReducibility true in
attribute [local irreducible] moduleIdentity derivedIdentity moduleTransport derivedTransport
  inverseImageCompletedCoefficientMap

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective in
private theorem moduleComposition_apply
    {Z W V : Scheme.{u}} (h : Z ⟶ W) (k : W ⟶ V) [IsIso h] [IsIso k]
    (M : integralTowerModules l E V) (U : Z.ProEt)
    (x : ((inverseImageIntegralModules l E k ⋙
      inverseImageIntegralModules l E h).obj M).val.obj (op U)) :
    ((integralInverseImageComposition l E h k).hom.app M).val.app (op U) x =
      M.val.map ((MorphismProperty.Over.mapComp (Q := ⊤)
        (inferInstance : WeaklyEtale h) (inferInstance : WeaklyEtale k)).hom.app U).op x :=
  (integralInverseImageComposition_existsUnique l E h k).exists.choose_spec M U x

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective in
private theorem moduleComposition_unit (X : Scheme.{u}) :
    (integralInverseImageComposition l E (𝟙 X) (𝟙 X)).hom ≫
        (moduleTransport l E X (Category.id_comp (𝟙 X))).hom =
      Functor.whiskerRight (moduleIdentity l E X).hom
        (inverseImageIntegralModules l E (𝟙 X)) ≫
          (Functor.leftUnitor (inverseImageIntegralModules l E (𝟙 X))).hom := by
  apply NatTrans.ext
  funext M
  apply (cancel_mono ((moduleIdentity l E X).hom.app M)).1
  have h := integralIdentityCompositorSections l E X (moduleIdentity l E X)
    (moduleTransport l E X (Category.id_comp (𝟙 X)) ≪≫ moduleIdentity l E X)
    (moduleIdentity_apply l E X) (moduleReturn_apply l E X _ _)
  simpa only [NatTrans.comp_app, Iso.trans_hom, Category.assoc] using congr_app h M

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective in
private theorem moduleComposition_counit {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] :
    (integralInverseImageComposition l E (inv g) g).hom ≫
        (moduleTransport l E Y (IsIso.inv_hom_id g) ≪≫ moduleIdentity l E Y).hom =
      (pullbackIdentityModuleCounit l E g).hom := by
  ext M U x
  change ((moduleTransport l E Y (IsIso.inv_hom_id g) ≪≫ moduleIdentity l E Y).hom.app M).val.app U
        (((integralInverseImageComposition l E (inv g) g).hom.app M).val.app U x) = _
  rw [moduleReturn_apply]
  have hd : ((integralInverseImageComposition l E (inv g) g).hom.app M).val.app U x =
      M.val.map ((MorphismProperty.Over.mapComp (Q := ⊤)
        (inferInstance : WeaklyEtale (inv g))
        (inferInstance : WeaklyEtale g)).hom.app U.unop).op x :=
    moduleComposition_apply l E (inv g) g M U.unop x
  have hc : ((pullbackIdentityModuleCounit l E g).hom.app M).val.app U x =
      M.val.map ((pullbackIdentitySiteUnit g).hom.app U.unop).op x :=
    (pullbackIdentityModuleCounit_existsUnique l E g).exists.choose_spec M U.unop x
  rw [hd, hc]
  change M.val.presheaf.map _ (M.val.presheaf.map _ x) = M.val.presheaf.map _ x
  rw [← ConcreteCategory.comp_apply, ← CategoryTheory.Functor.map_comp]
  rfl

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective in
private theorem derivedIso_trans
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    (F G H : A ⥤ B) [F.Additive] [G.Additive] [H.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (e : F ≅ G) (r : G ≅ H) :
    (Functor.mapDerivedCategoryNatIso (e ≪≫ r)).hom =
      (Functor.mapDerivedCategoryNatIso e).hom ≫
        (Functor.mapDerivedCategoryNatIso r).hom := by
  apply Localization.natTrans_ext DerivedCategory.Q (HomologicalComplex.quasiIso A (.up ℤ))
  intro K
  apply (cancel_mono (H.mapDerivedCategoryFactors.hom.app K)).1
  change _ = ((Functor.mapDerivedCategoryNatIso e).hom.app _ ≫
    (Functor.mapDerivedCategoryNatIso r).hom.app _) ≫ _
  rw [Functor.mapDerivedCategoryNatIso_fac, Category.assoc,
    Functor.mapDerivedCategoryNatIso_fac, ← Category.assoc,
    Functor.mapDerivedCategoryNatIso_fac, Category.assoc, ← Functor.map_comp]
  rfl

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective in
private theorem derivedIso_transport (X : Scheme.{u}) {f g : X ⟶ X}
    [IsIso f] [IsIso g] (w : f = g) :
    (Functor.mapDerivedCategoryNatIso (moduleTransport l E X w)).hom =
      (derivedTransport l E X w).hom := by
  subst g
  apply Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso (integralTowerModules l E X) (.up ℤ))
  intro K
  apply (cancel_mono
    ((inverseImageIntegralModules l E f).mapDerivedCategoryFactors.hom.app K)).1
  rw [Functor.mapDerivedCategoryNatIso_fac]
  simp only [moduleTransport, derivedTransport, Iso.refl_hom,
    NatTrans.id_app, Category.id_comp]
  change _ ≫ DerivedCategory.Q.map (𝟙 _) = _
  rw [CategoryTheory.Functor.map_id, Category.comp_id]

private theorem leftUnitor_hom_eq
    {A B : Type*} [Category A] [Category B] (F : A ⥤ B) :
    (Functor.leftUnitor F).hom = 𝟙 F := by
  rfl

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective in
private theorem deriveUnit
    {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
    (F : A ⥤ A) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (e : F ≅ 𝟭 A) (c : F ⋙ F ≅ F)
    (hc : c.hom = Functor.whiskerRight e.hom F ≫ (Functor.leftUnitor F).hom) :
    (Functor.mapDerivedCategoryCompIso F F).inv ≫
        (Functor.mapDerivedCategoryNatIso c).hom =
      Functor.whiskerRight ((Functor.mapDerivedCategoryNatIso e).hom ≫
        (Functor.mapDerivedCategoryIdIso A).hom) F.mapDerivedCategory ≫
          (Functor.leftUnitor F.mapDerivedCategory).hom := by
  let C : Unit → Type _ := fun _ ↦ A
  let W : ExactDerivedPasting.Word C () () := .edge (ExactFunctor.of F)
  let a : ExactDerivedPasting.Expression C (.comp W W) W := .cell c.hom
  let b : ExactDerivedPasting.Expression C (.comp W W) W :=
    .vcomp (.output (.cell (P := W) (R := .nil ()) e.hom) W) (.leftUnit W)
  have hab : a.ordinary = b.ordinary := by
    change c.hom = Functor.whiskerRight e.hom F ≫ (Functor.leftUnitor F).hom
    exact hc
  have h := (ExactDerivedPasting.exact_derived_transformation_pasting C).2.1 a b hab
  simpa only [C, a, b, W, ExactDerivedPasting.Expression.derived,
    ExactDerivedPasting.Word.cell, ExactDerivedPasting.Word.comparison,
    ExactDerivedPasting.Word.ordinary, ExactDerivedPasting.Word.derived,
    ExactFunctor.of_fst, Iso.trans_hom, Iso.trans_inv, Iso.refl_hom, Iso.refl_inv,
    Iso.symm_hom, Functor.mapDerivedCategoryNatIso, NatIso.mapHomologicalComplex,
    Localization.liftNatIso_hom,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerLeft_inv,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerRight_inv,
    Functor.whiskerLeft_id', Functor.whiskerRight_id',
    Category.id_comp, Category.comp_id] using h

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective in
private theorem derivedComposition_unit (X : Scheme.{u}) :
    (integralInverseImageDerivedComposition l E (𝟙 X) (𝟙 X)).hom ≫
        (derivedTransport l E X (Category.id_comp (𝟙 X))).hom =
      Functor.whiskerRight (derivedIdentity l E X).hom
        (inverseImageIntegralDerived l E (𝟙 X)) ≫
          (Functor.leftUnitor (inverseImageIntegralDerived l E (𝟙 X))).hom := by
  let d := integralInverseImageComposition l E (𝟙 X) (𝟙 X)
  let t := moduleTransport l E X (Category.id_comp (𝟙 X))
  have h := deriveUnit (inverseImageIntegralModules l E (𝟙 X))
    (moduleIdentity l E X) (d ≪≫ t) (moduleComposition_unit l E X)
  rw [derivedIso_trans] at h
  rw [derivedIso_transport] at h
  simpa only [integralInverseImageDerivedComposition, derivedIdentity,
    Iso.trans_hom, Iso.symm_hom, Category.assoc] using h

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective in
private theorem kappa_transport {X : Scheme.{u}} {f g : X ⟶ X}
    [IsIso f] [IsIso g] (w : f = g)
    (hX : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
    (hY : ∀ y : X, IsUnit (l : X.presheaf.stalk y))
    (N : DerivedCategory (integralTowerModules l E X)) :
    inverseImagePullbackComparisonDerived l E f hX hY N ≫
        eqToHom (congrArg (fun f ↦ (integralDerivedPullback l E f).obj N) w) =
      (derivedTransport l E X w).hom.app N ≫
        inverseImagePullbackComparisonDerived l E g hX hY N := by
  subst g
  simp only [derivedTransport, Iso.refl_hom, NatTrans.id_app,
    eqToHom_refl, Category.id_comp, Category.comp_id]

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective in
private theorem derivedReturn (X : Scheme.{u}) (f : X ⟶ X) [IsIso f] (w : f = 𝟙 X) :
    (Functor.mapDerivedCategoryNatIso
        (moduleTransport l E X w ≪≫
          moduleIdentity l E X)).hom ≫ (Functor.mapDerivedCategoryIdIso _).hom =
      (derivedTransport l E X w ≪≫
        derivedIdentity l E X).hom := by
  subst f
  simp only [moduleTransport, derivedTransport, Iso.refl_trans,
    derivedIdentity, Iso.trans_hom]

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective in
private theorem derivedComposition_counit {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] :
    (integralInverseImageDerivedComposition l E (inv g) g).hom ≫
        (derivedTransport l E Y (IsIso.inv_hom_id g) ≪≫ derivedIdentity l E Y).hom =
      (pullbackIdentityInverseImageCounit l E g).hom := by
  rw [← derivedReturn]
  dsimp only [integralInverseImageDerivedComposition,
    pullbackIdentityInverseImageCounit, Iso.trans_hom, Iso.symm_hom]
  simp only [Category.assoc]
  have hc : integralInverseImageComposition l E (inv g) g ≪≫
      (moduleTransport l E Y (IsIso.inv_hom_id g) ≪≫ moduleIdentity l E Y) =
        pullbackIdentityModuleCounit l E g :=
    Iso.ext (moduleComposition_counit l E g)
  have ht := derivedIso_trans _ _ _ (integralInverseImageComposition l E (inv g) g)
    (moduleTransport l E Y (IsIso.inv_hom_id g) ≪≫ moduleIdentity l E Y)
  rw [hc] at ht
  rw [← reassoc_of% ht]

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective in
private theorem kappa_identity
    (C : IntegralComparisonSystem.{u} l) (X : Scheme.{u})
    [∀ x : X, Invertible (l : X.residueField x)]
    (hX : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
    (K : sfIntegralConstructibleCategory l E X) :
    inverseImagePullbackComparisonDerived l E (𝟙 X) hX hX K.obj ≫
        (integralComparisonUnit l E C X K).hom =
      (derivedIdentity l E X).hom.app K.obj := by
  let G := inverseImageIntegralDerived l E (𝟙 X)
  let P := integralDerivedPullback l E (𝟙 X)
  let U := integralComparisonUnit l E C X K
  obtain ⟨κ, hk, _⟩ := inverseImagePullbackComparisonIntegral_natural.{u, u, 0, 0}
    l E (𝟙 X) hX hX
  haveI : IsIso (κ.app K.obj) := by
    rw [hk]
    exact pullbackIdentityKappa_isIso l E (𝟙 X) hX hX K
  haveI : G.Faithful := Functor.Faithful.of_iso (derivedIdentity l E X).symm
  apply G.map_injective
  apply (cancel_mono (κ.app K.obj)).1
  have hcomp := (integralInverseImageComparison_composition l E C (𝟙 X) (𝟙 X) K).2
  have hun := (normalizedIntegralGeometricCoherence l C E).unitTarget (𝟙 X) K
  have hn := κ.naturality U.hom
  calc
    G.map (inverseImagePullbackComparisonDerived l E (𝟙 X) hX hX K.obj ≫ U.hom) ≫
        κ.app K.obj =
      G.map (κ.app K.obj) ≫ κ.app (P.obj K.obj) ≫ P.map U.hom := by
        rw [← hk K.obj, Functor.map_comp, Category.assoc, hn]
    _ = (integralInverseImageDerivedComposition l E (𝟙 X) (𝟙 X)).hom.app K.obj ≫
        inverseImagePullbackComparisonDerived l E ((𝟙 X) ≫ (𝟙 X)) hX hX K.obj ≫
        (integralComparisonComposition l E C (𝟙 X) (𝟙 X) K).hom ≫ P.map U.hom := by
      simpa only [hk, G, P, Category.assoc] using
        congrArg (fun f ↦ f ≫ P.map U.hom) hcomp.symm
    _ = (integralInverseImageDerivedComposition l E (𝟙 X) (𝟙 X)).hom.app K.obj ≫
        (derivedTransport l E X (Category.id_comp (𝟙 X))).hom.app K.obj ≫ κ.app K.obj := by
      rw [hun, kappa_transport l E (Category.id_comp (𝟙 X)) hX hX]
      rw [hk]
    _ = G.map ((derivedIdentity l E X).hom.app K.obj) ≫ κ.app K.obj := by
      have hu := congr_app (derivedComposition_unit l E X) K.obj
      change (integralInverseImageDerivedComposition l E (𝟙 X) (𝟙 X)).hom.app K.obj ≫
        (derivedTransport l E X (Category.id_comp (𝟙 X))).hom.app K.obj =
          G.map ((derivedIdentity l E X).hom.app K.obj) ≫ 𝟙 _ at hu
      have hu' := hu.trans (Category.comp_id (G.map ((derivedIdentity l E X).hom.app K.obj)))
      simpa only [Category.assoc] using congrArg (fun f ↦ f ≫ κ.app K.obj) hu'


attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective in
/-- Precomposition identity for inverse cancellation.

Source: the Weil-structures paragraph, parent node steps 4--6.
(blueprint: lem-sf-integral-automorphism-cancellation-precomposition).

Proof: expand the specified epsilon into the inverse kappa factors and ordinary
counit, apply the actual kappa composition law, transport across the inverse
identity, and use the normalized identity unit. This is the strictly simpler
precomposed equality; the parent theorem cancels its invertible precomposition. -/
theorem integralAutomorphismCancellation_precomposition
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (C : IntegralComparisonSystem.{u} l) {X Y : Scheme.{u}}
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (g : X ⟶ Y) [IsIso g] (K : sfIntegralConstructibleCategory l E Y) :
    let hX : ∀ x : X, IsUnit (l : X.presheaf.stalk x) := fun x ↦
      isUnit_of_map_unit (IsLocalRing.residue (X.presheaf.stalk x)) _
        ((map_natCast (IsLocalRing.residue (X.presheaf.stalk x)) l).symm ▸
          isUnit_of_invertible (l : X.residueField x))
    let hY : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y) := fun y ↦
      isUnit_of_map_unit (IsLocalRing.residue (Y.presheaf.stalk y)) _
        ((map_natCast (IsLocalRing.residue (Y.presheaf.stalk y)) l).symm ▸
          isUnit_of_invertible (l : Y.residueField y))
    let A := (inverseImageIntegralDerived l E (inv g)).map
      (inverseImagePullbackComparisonDerived l E g hX hY K.obj) ≫
      inverseImagePullbackComparisonDerived l E (inv g) hY hX
        ((constructibleIntegralPullback l E g).obj K).obj
    HEq (A ≫ (pullbackIdentityEpsilon l E g K).hom)
      (A ≫ ((integralComparisonComposition l E C (inv g) g K).symm ≪≫
        eqToIso (congrArg (fun f ↦ (integralDerivedPullback l E f).obj K.obj)
          (IsIso.inv_hom_id g)) ≪≫ integralComparisonUnit l E C Y K).hom) := by
  dsimp only
  apply heq_of_eq
  let hX : ∀ x : X, IsUnit (l : X.presheaf.stalk x) := fun x ↦
    isUnit_of_map_unit (IsLocalRing.residue (X.presheaf.stalk x)) _
      ((map_natCast (IsLocalRing.residue (X.presheaf.stalk x)) l).symm ▸
        isUnit_of_invertible (l : X.residueField x))
  let hY : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y) := fun y ↦
    isUnit_of_map_unit (IsLocalRing.residue (Y.presheaf.stalk y)) _
      ((map_natCast (IsLocalRing.residue (Y.presheaf.stalk y)) l).symm ▸
        isUnit_of_invertible (l : Y.residueField y))
  let G := inverseImageIntegralDerived l E (inv g)
  let κg := inverseImagePullbackComparisonDerived l E g hX hY K.obj
  let κh := inverseImagePullbackComparisonDerived l E (inv g) hY hX
    ((constructibleIntegralPullback l E g).obj K).obj
  let A := G.map κg ≫ κh
  let c := integralComparisonComposition l E C (inv g) g K
  let d := integralInverseImageDerivedComposition l E (inv g) g
  let U := integralComparisonUnit l E C Y K
  let tP := eqToHom (congrArg (fun f ↦ (integralDerivedPullback l E f).obj K.obj)
    (IsIso.inv_hom_id g))
  let tG := (derivedTransport l E Y (IsIso.inv_hom_id g)).hom.app K.obj
  haveI : IsIso κg := pullbackIdentityKappa_isIso l E g hX hY K
  haveI : IsIso κh := pullbackIdentityKappa_isIso l E (inv g) hY hX
    ((constructibleIntegralPullback l E g).obj K)
  change A ≫ (pullbackIdentityEpsilon l E g K).hom = A ≫ c.inv ≫ tP ≫ U.hom
  have hleft : A ≫ (pullbackIdentityEpsilon l E g K).hom =
      (pullbackIdentityInverseImageCounit l E g).hom.app K.obj := by
    unfold pullbackIdentityEpsilon pullbackIdentityLambda
    simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, asIso_inv, Iso.app_hom]
    change (G.map κg ≫ κh) ≫
      (inv κh ≫ G.map (inv κg) ≫
        (pullbackIdentityInverseImageCounit l E g).hom.app K.obj) = _
    rw [Category.assoc, IsIso.hom_inv_id_assoc, ← G.map_comp_assoc,
      IsIso.hom_inv_id, G.map_id, Category.id_comp]
  have hcomp := (integralInverseImageComparison_composition l E C (inv g) g K).2
  change d.hom.app K.obj ≫
    inverseImagePullbackComparisonDerived l E (inv g ≫ g) hY hY K.obj ≫ c.hom = A
    at hcomp
  rw [hleft]
  symm
  calc
    A ≫ c.inv ≫ tP ≫ U.hom = d.hom.app K.obj ≫
        inverseImagePullbackComparisonDerived l E (inv g ≫ g) hY hY K.obj ≫
        tP ≫ U.hom := by
      rw [← hcomp]
      simp only [Category.assoc, Iso.hom_inv_id_assoc]
    _ = d.hom.app K.obj ≫ tG ≫
        inverseImagePullbackComparisonDerived l E (𝟙 Y) hY hY K.obj ≫ U.hom := by
      rw [reassoc_of% (kappa_transport l E (IsIso.inv_hom_id g) hY hY K.obj)]
    _ = d.hom.app K.obj ≫ tG ≫ (derivedIdentity l E Y).hom.app K.obj := by
      rw [kappa_identity l E C Y hY K]
    _ = (pullbackIdentityInverseImageCounit l E g).hom.app K.obj := by
      simpa only [NatTrans.comp_app, Iso.trans_hom, eqToIso.hom,
        eqToHom_app, Category.assoc, d, tG] using
        congr_app (derivedComposition_counit l E g) K.obj

end WeilConjectures
