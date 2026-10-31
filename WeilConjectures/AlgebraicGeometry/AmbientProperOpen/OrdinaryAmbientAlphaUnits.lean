/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AmbientProperOpen.AmbientProperOpenCalculus
import WeilConjectures.AlgebraicGeometry.AmbientClopen.UnderivedPasting.Systems.AmbientUnderivedClopenPasting
import all WeilConjectures.AlgebraicGeometry.AmbientClopen.AmbientOrdinaryClopenLocalization
import WeilConjectures.CategoryTheory.ExactDerivedPasting.Word.ExactDerivedTransformationPasting

/-! # Ordinary derived clopen comparisons

Source: Stacks Project, Tags 0F7B--0F7D, 015F and 07A7.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u v w
open CategoryTheory AlgebraicGeometry
namespace AlgebraicGeometry.ProEtale.AmbientProperOpen

attribute [local irreducible] Functor.mapDerivedCategory Functor.leftDerivedFunctor
  upperStar lowerStar Functor.rightDerivedFunctor
  Functor.leftAdjoint constantSheaf properOpenAlpha AmbientClopen.alpha

section ExactUnits
open AmbientClopen ExactDerivedPasting
variable (C : Fin 2 → Type u) [∀ i, Category.{v} (C i)]
  [∀ i, Abelian (C i)] [∀ i, HasDerivedCategory.{w} (C i)]

-- Interpret the identity word as a finite pasting expression before localizing.
private theorem exact_vertical_unit
    (F : C 0 ⥤ₑ C 1) (I : C 1 ⥤ₑ C 1) (H : C 0 ⥤ₑ C 0)
    [F.obj.Additive] [I.obj.Additive] [H.obj.Additive]
    (eI : I.obj ≅ 𝟭 (C 1)) (eH : H.obj ≅ 𝟭 (C 0))
    (a : F.obj ⋙ I.obj ⟶ H.obj ⋙ F.obj)
    (ha : a = Functor.whiskerLeft F.obj eI.hom ≫
      (Functor.rightUnitor F.obj).hom ≫ (Functor.leftUnitor F.obj).inv ≫
      Functor.whiskerRight eH.inv F.obj) :
    localizeSquare F.obj I.obj H.obj F.obj a =
      Functor.whiskerLeft F.obj.mapDerivedCategory
        (Functor.mapDerivedCategoryNatIso eI ≪≫ Functor.mapDerivedCategoryIdIso _).hom ≫
      (Functor.rightUnitor _).hom ≫ (Functor.leftUnitor _).inv ≫
      Functor.whiskerRight
        (Functor.mapDerivedCategoryNatIso eH ≪≫ Functor.mapDerivedCategoryIdIso _).inv
        F.obj.mapDerivedCategory := by
  let f := Word.edge F
  let i := Word.edge I
  let h := Word.edge H
  let x : Expression C (.comp f i) (.comp h f) :=
    .vcomp (.input f (.cell (P := i) (R := .nil 1) eI.hom))
      (.vcomp (.rightUnit f) (.vcomp (.leftUnitInv f)
        (.output (.cell (P := .nil 0) (R := h) eH.inv) f)))
  have hx := (exact_derived_transformation_pasting C).1 x
  have ho : x.ordinary = a := ha.symm
  rw [ho] at hx
  simpa only [x, f, i, h, Expression.derived, Word.cell, Word.comparison,
    Word.ordinary, Word.derived, Iso.trans_hom, Iso.trans_inv,
    Iso.refl_hom, Iso.refl_inv, Functor.isoWhiskerLeft_refl,
    Functor.isoWhiskerRight_refl, Category.comp_id, Category.id_comp,
    ExactFunctor.of_fst, localizeSquare, localize, Functor.whiskerLeft_comp,
    Functor.whiskerRight_comp, Category.assoc, Functor.mapDerivedCategoryNatIso,
    Localization.liftNatIso_hom, Localization.liftNatIso_inv,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerRight_inv,
    NatIso.mapHomologicalComplex] using hx.symm

private theorem exact_horizontal_unit
    (F : C 0 ⥤ₑ C 1) (I : C 1 ⥤ₑ C 1) (H : C 0 ⥤ₑ C 0)
    [F.obj.Additive] [I.obj.Additive] [H.obj.Additive]
    (eI : I.obj ≅ 𝟭 (C 1)) (eH : H.obj ≅ 𝟭 (C 0))
    (a : H.obj ⋙ F.obj ⟶ F.obj ⋙ I.obj)
    (ha : a = Functor.whiskerRight eH.hom F.obj ≫
      (Functor.leftUnitor F.obj).hom ≫ (Functor.rightUnitor F.obj).inv ≫
      Functor.whiskerLeft F.obj eI.inv) :
    localizeSquare H.obj F.obj F.obj I.obj a =
      Functor.whiskerRight
        (Functor.mapDerivedCategoryNatIso eH ≪≫ Functor.mapDerivedCategoryIdIso _).hom
        F.obj.mapDerivedCategory ≫
      (Functor.leftUnitor _).hom ≫ (Functor.rightUnitor _).inv ≫
      Functor.whiskerLeft F.obj.mapDerivedCategory
        (Functor.mapDerivedCategoryNatIso eI ≪≫ Functor.mapDerivedCategoryIdIso _).inv := by
  let f := Word.edge F
  let i := Word.edge I
  let h := Word.edge H
  let x : Expression C (.comp h f) (.comp f i) :=
    .vcomp (.output (.cell (P := h) (R := .nil 0) eH.hom) f)
      (.vcomp (.leftUnit f) (.vcomp (.rightUnitInv f)
        (.input f (.cell (P := .nil 1) (R := i) eI.inv))))
  have hx := (exact_derived_transformation_pasting C).1 x
  have ho : x.ordinary = a := ha.symm
  rw [ho] at hx
  simpa only [x, f, i, h, Expression.derived, Word.cell, Word.comparison,
    Word.ordinary, Word.derived, Iso.trans_hom, Iso.trans_inv,
    Iso.refl_hom, Iso.refl_inv, Functor.isoWhiskerLeft_refl,
    Functor.isoWhiskerRight_refl, Category.comp_id, Category.id_comp,
    ExactFunctor.of_fst, localizeSquare, localize, Functor.whiskerLeft_comp,
    Functor.whiskerRight_comp, Category.assoc, Functor.mapDerivedCategoryNatIso,
    Localization.liftNatIso_hom, Localization.liftNatIso_inv,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerRight_inv,
    NatIso.mapHomologicalComplex] using hx.symm

-- The inverse identity comparison is the unit followed by the right identity map.
attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem exact_left_id_localized
    {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    {L R : A ⥤ A} [L.Additive] [R.Additive]
    [Limits.PreservesFiniteLimits L] [Limits.PreservesFiniteColimits L]
    [Limits.PreservesFiniteLimits R] [Limits.PreservesFiniteColimits R]
    (a : L ⊣ R) (e : R ≅ 𝟭 A) :
    Functor.mapDerivedCategoryNatIso (Adjunction.leftAdjointIdIso a e) ≪≫
        Functor.mapDerivedCategoryIdIso A =
      Adjunction.leftAdjointIdIso a.mapExactDerivedCategory
        (Functor.mapDerivedCategoryNatIso e ≪≫ Functor.mapDerivedCategoryIdIso A) := by
  let D : Fin 1 → Type u := fun _ ↦ A
  let : ∀ i, Category.{v} (D i) := fun _ ↦ inferInstance
  let : ∀ i, Abelian (D i) := fun _ ↦ inferInstance
  let : ∀ i, HasDerivedCategory.{w} (D i) := fun _ ↦ inferInstance
  let l : Word D 0 0 := .edge (ExactFunctor.of L)
  let r : Word D 0 0 := .edge (ExactFunctor.of R)
  let x : Expression D (.nil 0) l :=
    .vcomp (.cell (P := .nil 0) (R := .comp l r) a.unit)
      (.vcomp (.input l (.cell (P := r) (R := .nil 0) e.hom)) (.rightUnit l))
  have ho : x.ordinary = (Adjunction.leftAdjointIdIso a e).inv := by
    ext M
    simp only [x, l, r, Expression.ordinary, Word.ordinary, ExactFunctor.of_fst,
      NatTrans.comp_app, Functor.whiskerLeft_app, Functor.rightUnitor_hom_app,
      Adjunction.leftAdjointIdIso_inv_app]
    change a.unit.app M ≫ e.hom.app (L.obj M) ≫ 𝟙 _ =
      a.unit.app M ≫ e.hom.app (L.obj M)
    rw [Category.comp_id]
  have hx := (exact_derived_transformation_pasting D).1 x
  rw [ho] at hx
  have hu := AmbientClopen.localize_adjunction_unit a
  apply Iso.ext_inv
  apply NatTrans.ext
  funext M
  have ht := congrArg (fun t ↦ t.app M) hx
  simp only [x, l, r, Expression.derived, Word.cell, Word.comparison, Word.ordinary,
    Word.derived, Iso.trans_hom, Iso.refl_hom, Iso.refl_inv,
    Functor.isoWhiskerLeft_refl, Functor.isoWhiskerRight_refl,
    Category.comp_id, Category.id_comp, ExactFunctor.of_fst] at ht
  dsimp only [D] at ht
  change ((Functor.mapDerivedCategoryIdIso A).inv ≫ localize a.unit ≫
      (Functor.mapDerivedCategoryCompIso L R).hom).app M ≫
      (localize e.hom ≫ (Functor.mapDerivedCategoryIdIso A).hom).app
        (L.mapDerivedCategory.obj M) ≫ 𝟙 _ =
    ((Functor.mapDerivedCategoryIdIso A).inv ≫
      localize (Adjunction.leftAdjointIdIso a e).inv).app M at ht
  rw [Category.comp_id] at ht
  rw [Adjunction.leftAdjointIdIso_inv_app, ← hu]
  simpa only [Adjunction.leftAdjointIdIso_inv_app, Iso.trans_hom, Iso.trans_inv,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerLeft_comp,
    Functor.rightUnitor_hom_app, Category.comp_id, Category.assoc,
    Functor.mapDerivedCategoryNatIso, Localization.liftNatIso_inv,
    Localization.liftNatIso_hom, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerRight_inv, NatIso.mapHomologicalComplex, localize] using ht.symm

end ExactUnits

-- Compare the two identity-adjoint normalizations after changing the right adjoint.
private theorem left_id_transport
    {A : Type*} [Category A] {L R R' : A ⥤ A}
    (a : L ⊣ R) (f : R ≅ R') (e : R' ≅ 𝟭 A) :
    (a.ofNatIsoRight f).leftAdjointUniq (Adjunction.id.ofNatIsoRight e.symm) =
      Adjunction.leftAdjointIdIso a (f ≪≫ e) := by
  apply Iso.ext_inv
  ext M
  simp [Adjunction.leftAdjointUniq, Adjunction.leftAdjointIdIso,
    conjugateIsoEquiv, conjugateEquiv_symm_apply_app, Adjunction.ofNatIsoRight]

open AmbientClopen UnderivedPasting

-- The total pullback identity is the exact identity through the total/exact comparison.
private theorem pull_id_localized
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] (X : Scheme.{u}) :
    leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) (𝟙 X) ≪≫
        (Functor.mapDerivedCategoryNatIso (upperStarId (ModuleCat.{u + 1} Λ) X) ≪≫
          Functor.mapDerivedCategoryIdIso _) =
      leftDerivedUpperStarId (ModuleCat.{u + 1} Λ) X := by
  simp only [leftDerivedUpperStarId, Functor.leftDerivedFunctorNatIso,
    leftDerivedUpperStarIsoMapDerivedCategory, Iso.trans_assoc,
    Iso.symm_self_id_assoc]

private theorem open_id_localized
    (F : WeilConjectures.FiniteFieldDatum.{u})
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] (X : Spaces F) :
    (ordinary F Λ).jId X =
      Functor.mapDerivedCategoryNatIso (Ordinary.openIdentity Λ X.obj.left) ≪≫
        Functor.mapDerivedCategoryIdIso _ := by
  dsimp only [Calculus.jId, ordinary]
  change (properOpenAdj Λ (𝟙 X.obj.left)).leftAdjointUniq
    (Adjunction.id.ofNatIsoRight
      (leftDerivedUpperStarId (ModuleCat.{u + 1} Λ) X.obj.left).symm) = _
  rw [properOpenAdj, left_id_transport, AmbientClopen.ordinary_open_adjunction_exact]
  have he : (leftDerivedUpperStarIsoMapDerivedCategory
      (ModuleCat.{u + 1} Λ) (𝟙 X.obj.left)).symm ≪≫
      leftDerivedUpperStarId (ModuleCat.{u + 1} Λ) X.obj.left =
        Functor.mapDerivedCategoryNatIso (upperStarId (ModuleCat.{u + 1} Λ) X.obj.left) ≪≫
          Functor.mapDerivedCategoryIdIso _ := by
    rw [← pull_id_localized Λ X.obj.left]
    simp only [Iso.symm_self_id_assoc]
  rw [he, ← exact_left_id_localized]
  rfl

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem derived_vertical_unit
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (h : j ≫ 𝟙 X = 𝟙 U ≫ j)
    (ha : AmbientClopen.alpha Λ j (𝟙 U) (𝟙 X) j h =
      Functor.whiskerLeft (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j)
        (upperStarId (ModuleCat.{u + 1} Λ) X).hom ≫
      (Functor.rightUnitor _).hom ≫ (Functor.leftUnitor _).inv ≫
      Functor.whiskerRight (upperStarId (ModuleCat.{u + 1} Λ) U).inv
        (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j))
    (M : ProperOpenDerived Λ U) :
    (properOpenAlpha Λ j (𝟙 U) (𝟙 X) j h).app M ≫
        (ProperOpenShriek Λ j).map
          ((leftDerivedUpperStarId (ModuleCat.{u + 1} Λ) U).hom.app M) =
      (leftDerivedUpperStarId (ModuleCat.{u + 1} Λ) X).hom.app
        ((ProperOpenShriek Λ j).obj M) := by
  let D (i : Fin 2) := Sheaf (Scheme.ProEt.topology (![U, X] i)) (ModuleCat.{u + 1} Λ)
  let catD : ∀ i, Category.{u + 1} (D i) := fun _ ↦ inferInstance
  let abD : ∀ i, Abelian (D i) := fun _ ↦ inferInstance
  let derD : ∀ i, HasDerivedCategory.{u + 1} (D i) := fun _ ↦ inferInstance
  have : (ExactFunctor.of
      (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j)).obj.Additive := by
    change (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j).Additive
    infer_instance
  have : (ExactFunctor.of (upperStar (ModuleCat.{u + 1} Λ) (𝟙 X))).obj.Additive := by
    change (upperStar (ModuleCat.{u + 1} Λ) (𝟙 X)).Additive
    infer_instance
  have : (ExactFunctor.of (upperStar (ModuleCat.{u + 1} Λ) (𝟙 U))).obj.Additive := by
    change (upperStar (ModuleCat.{u + 1} Λ) (𝟙 U)).Additive
    infer_instance
  have hx : localizeSquare
      (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j)
      (upperStar (ModuleCat.{u + 1} Λ) (𝟙 X))
      (upperStar (ModuleCat.{u + 1} Λ) (𝟙 U))
      (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j)
      (AmbientClopen.alpha Λ j (𝟙 U) (𝟙 X) j h) =
      Functor.whiskerLeft
        (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j).mapDerivedCategory
        (Functor.mapDerivedCategoryNatIso (upperStarId (ModuleCat.{u + 1} Λ) X) ≪≫
          Functor.mapDerivedCategoryIdIso
            (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))).hom ≫
      (Functor.rightUnitor _).hom ≫ (Functor.leftUnitor _).inv ≫
      Functor.whiskerRight
        (Functor.mapDerivedCategoryNatIso (upperStarId (ModuleCat.{u + 1} Λ) U) ≪≫
          Functor.mapDerivedCategoryIdIso
            (Sheaf (Scheme.ProEt.topology U) (ModuleCat.{u + 1} Λ))).inv
        (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j).mapDerivedCategory :=
    exact_vertical_unit D
      (ExactFunctor.of (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j))
      (ExactFunctor.of (upperStar (ModuleCat.{u + 1} Λ) (𝟙 X)))
      (ExactFunctor.of (upperStar (ModuleCat.{u + 1} Λ) (𝟙 U)))
      (upperStarId (ModuleCat.{u + 1} Λ) X) (upperStarId (ModuleCat.{u + 1} Λ) U)
      (AmbientClopen.alpha Λ j (𝟙 U) (𝟙 X) j h) ha
  dsimp only [ProperOpenShriek]
  rw [← ordinary_alpha_localized, derivedAlpha, hx,
    ← pull_id_localized Λ U, ← pull_id_localized Λ X]
  simp only [Iso.trans_hom, Iso.trans_inv, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.rightUnitor_hom_app, Functor.leftUnitor_inv_app,
    Functor.map_comp, Category.assoc, Category.id_comp, Iso.symm_hom]
  simp only [← Functor.map_comp, Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app]
  simp only [ProperOpenShriek, CategoryTheory.Functor.map_id, Functor.id_obj,
    Category.comp_id]
  erw [Category.comp_id]

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem derived_horizontal_unit
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {U X : Scheme.{u}} (p : U ⟶ X) [IsProper p]
    (h : (𝟙 U) ≫ p = p ≫ (𝟙 X))
    (ha : AmbientClopen.alpha Λ (𝟙 U) p p (𝟙 X)
        h =
      Functor.whiskerRight (Ordinary.openIdentity Λ X).hom
        (upperStar (ModuleCat.{u + 1} Λ) p) ≫
      (Functor.leftUnitor _).hom ≫ (Functor.rightUnitor _).inv ≫
      Functor.whiskerLeft (upperStar (ModuleCat.{u + 1} Λ) p)
        (Ordinary.openIdentity Λ U).inv)
    (M : ProperOpenDerived Λ X) :
    (properOpenAlpha Λ (𝟙 U) p p (𝟙 X) h).app M ≫
        (Functor.mapDerivedCategoryNatIso (Ordinary.openIdentity Λ U) ≪≫
          Functor.mapDerivedCategoryIdIso _).hom.app ((ProperOpenPull Λ p).obj M) =
      (ProperOpenPull Λ p).map
        ((Functor.mapDerivedCategoryNatIso (Ordinary.openIdentity Λ X) ≪≫
          Functor.mapDerivedCategoryIdIso _).hom.app M) := by
  have : IsOpenImmersion (𝟙 U) := inferInstance
  have : IsOpenImmersion (𝟙 X) := inferInstance
  let D (i : Fin 2) := Sheaf (Scheme.ProEt.topology (![X, U] i))
    (ModuleCat.{u + 1} Λ)
  let catD : ∀ i, Category.{u + 1} (D i) := fun _ ↦ inferInstance
  let abD : ∀ i, Abelian (D i) := fun _ ↦ inferInstance
  let derD : ∀ i, HasDerivedCategory.{u + 1} (D i) := fun _ ↦ inferInstance
  have : (ExactFunctor.of
      (upperStar (ModuleCat.{u + 1} Λ) p)).obj.Additive := by
    change (upperStar (ModuleCat.{u + 1} Λ) p).Additive
    infer_instance
  have : (ExactFunctor.of (openImmersionLowerShriek
      (ModuleCat.{u + 1} Λ) (𝟙 U))).obj.Additive := by
    change (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) (𝟙 U)).Additive
    infer_instance
  have : (ExactFunctor.of (openImmersionLowerShriek
      (ModuleCat.{u + 1} Λ) (𝟙 X))).obj.Additive := by
    change (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) (𝟙 X)).Additive
    infer_instance
  have hx : localizeSquare
      (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) (𝟙 X))
      (upperStar (ModuleCat.{u + 1} Λ) p)
      (upperStar (ModuleCat.{u + 1} Λ) p)
      (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) (𝟙 U))
      (AmbientClopen.alpha Λ (𝟙 U) p p (𝟙 X) h) =
      Functor.whiskerRight
        (Functor.mapDerivedCategoryNatIso (Ordinary.openIdentity Λ X) ≪≫
          Functor.mapDerivedCategoryIdIso
            (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))).hom
        (upperStar (ModuleCat.{u + 1} Λ) p).mapDerivedCategory ≫
      (Functor.leftUnitor _).hom ≫ (Functor.rightUnitor _).inv ≫
      Functor.whiskerLeft (upperStar (ModuleCat.{u + 1} Λ) p).mapDerivedCategory
        (Functor.mapDerivedCategoryNatIso (Ordinary.openIdentity Λ U) ≪≫
          Functor.mapDerivedCategoryIdIso
            (Sheaf (Scheme.ProEt.topology U) (ModuleCat.{u + 1} Λ))).inv :=
    exact_horizontal_unit D
      (ExactFunctor.of (upperStar (ModuleCat.{u + 1} Λ) p))
      (ExactFunctor.of (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) (𝟙 U)))
      (ExactFunctor.of (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) (𝟙 X)))
      (Ordinary.openIdentity Λ U) (Ordinary.openIdentity Λ X)
      (AmbientClopen.alpha Λ (𝟙 U) p p (𝟙 X) h) ha
  dsimp only [ProperOpenPull]
  rw [← ordinary_alpha_localized, derivedAlpha, hx]
  simp only [Iso.trans_hom, Iso.trans_inv, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.rightUnitor_inv_app, Functor.leftUnitor_hom_app,
    Category.assoc, Category.id_comp, Iso.symm_hom]
  erw [Category.id_comp]
  rw [← NatTrans.naturality_assoc, ← NatTrans.naturality_assoc,
    ← NatTrans.naturality_assoc]
  simp only [Functor.id_map, Functor.id_obj, Iso.hom_inv_id_app,
    Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app, Category.comp_id]

/-- Identity-square equations for the localized ordinary clopen arrow.
Source: Stacks Project, more-etale.tex, Tag 0F7B; derived.tex, Tag 015F;
sites-cohomology.tex, Tag 07A7
(blueprint: lem-sf-ordinary-ambient-alpha-units).

Proof: Take the two identity equations in the ordinary clause of
ambientUnderivedClopenPasting at level n. Apply exact derived localization to the
identity inverse-image and open-extension words. Exact localization preserves
composition and the unitors. The theorem
ordinary_alpha_localized identifies the localized clopen arrow with
properOpenAlpha, through the specified total-to-exact pullback comparison.
The pullback identity word becomes leftDerivedUpperStarId. For the open identity,
localization of the specified open adjunction identifies the left-adjoint identity
comparison with Calculus.jId; equivalently use uniqueness of its unit-normalized
adjunction transpose. Cancel the intermediate comparison isomorphisms. These are
the two displayed equations, including for empty schemes and zero objects. -/
theorem ordinaryAmbientAlphaUnits (F : WeilConjectures.FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (hl : l ≠ F.p)
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (n : ℕ) :
    let c := (ordinary F (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))))
    (∀ {U X : Spaces F} (j : U ⟶ X)
      [IsOpenImmersion ((geometry F).map j)] [QuasiCompact ((geometry F).map j)]
      (h : j ≫ (𝟙 X) = (𝟙 U) ≫ j) (M : c.D U),
      (c.alpha j (𝟙 U) (𝟙 X) j h).app M ≫
          (c.J j).map ((c.pId U).hom.app M) =
        (c.pId X).hom.app ((c.J j).obj M)) ∧
    (∀ {U X : Spaces F} (p : U ⟶ X) [IsProper ((geometry F).map p)]
      (h : (𝟙 U) ≫ p = p ≫ (𝟙 X)) (M : c.D X),
      (c.alpha (𝟙 U) p p (𝟙 X) h).app M ≫
          (c.jId U).hom.app ((c.P p).obj M) =
        (c.P p).map ((c.jId X).hom.app M)) := by
  let Λ := ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))
  have hi := ((UnderivedPasting.ambientUnderivedClopenPasting F l hl E).1 n).2.2
  constructor
  · intro U X j _ _ h M
    let : U.obj.left.Over (Spec (.of F.k)) := ⟨U.obj.hom⟩
    let : X.obj.left.Over (Spec (.of F.k)) := ⟨X.obj.hom⟩
    have : LocallyOfFiniteType (U.obj.left ↘ Spec (.of F.k)) := U.property.1
    have : QuasiCompact (U.obj.left ↘ Spec (.of F.k)) := U.property.2
    have : LocallyOfFiniteType (X.obj.left ↘ Spec (.of F.k)) := X.property.1
    have : QuasiCompact (X.obj.left ↘ Spec (.of F.k)) := X.property.2
    have : j.hom.left.IsOver (Spec (.of F.k)) := ⟨j.hom.w⟩
    have : IsOpenImmersion j.hom.left := inferInstanceAs
      (IsOpenImmersion ((geometry F).map j))
    have : QuasiCompact j.hom.left := inferInstanceAs
      (QuasiCompact ((geometry F).map j))
    exact derived_vertical_unit Λ j.hom.left (congrArg (fun f ↦ f.hom.left) h)
      (hi.1 U.obj.left X.obj.left j.hom.left _) M
  · intro U X p _ h M
    let : U.obj.left.Over (Spec (.of F.k)) := ⟨U.obj.hom⟩
    let : X.obj.left.Over (Spec (.of F.k)) := ⟨X.obj.hom⟩
    have : LocallyOfFiniteType (U.obj.left ↘ Spec (.of F.k)) := U.property.1
    have : QuasiCompact (U.obj.left ↘ Spec (.of F.k)) := U.property.2
    have : LocallyOfFiniteType (X.obj.left ↘ Spec (.of F.k)) := X.property.1
    have : QuasiCompact (X.obj.left ↘ Spec (.of F.k)) := X.property.2
    have : p.hom.left.IsOver (Spec (.of F.k)) := ⟨p.hom.w⟩
    have : IsProper p.hom.left := inferInstanceAs (IsProper ((geometry F).map p))
    rw [open_id_localized, open_id_localized]
    exact derived_horizontal_unit Λ p.hom.left (congrArg (fun f ↦ f.hom.left) h)
      (hi.2 U.obj.left X.obj.left p.hom.left _) M

end AlgebraicGeometry.ProEtale.AmbientProperOpen
