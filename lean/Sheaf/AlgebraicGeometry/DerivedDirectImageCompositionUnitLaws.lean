/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A3
-/
module

public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage

import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp

/-!
# Coherence of canonical unbounded derived direct images

Source: Stacks Project, Cohomology, Tag 0D5T and its derived universal property.
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Abelian

set_option autoImplicit false

namespace AlgebraicGeometry

private theorem moduleDirectImage_id (X : Scheme.{u}) :
    RingedSpace.moduleDirectImage (𝟙 X : X ⟶ X).toLRSHom.toShHom =
      𝟭 (SheafOfModules.{u} (moduleRings X.toRingedSpace)) := rfl

-- The identity localization is a right derived functor, since its unit is invertible.
private noncomputable def identity_unit
    (C : Type*) [Category C] [Abelian C] [HasDerivedCategory C] :
    (𝟭 C).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ 𝟭 (DerivedCategory C) :=
  Functor.whiskerRight (Functor.mapHomotopyCategoryIdIso C (ComplexShape.up ℤ)).hom
      DerivedCategory.Qh ≫
    DerivedCategory.Qh.leftUnitor.hom ≫ DerivedCategory.Qh.rightUnitor.inv

private theorem identity_unit_app
    (C : Type*) [Category C] [Abelian C] [HasDerivedCategory C]
    (K : HomotopyCategory C (ComplexShape.up ℤ)) :
    (identity_unit C).app K = 𝟙 _ := by
  simp only [identity_unit, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.leftUnitor_hom_app, Functor.rightUnitor_inv_app,
    Functor.mapHomotopyCategoryIdIso_hom_app_eq_id, Category.comp_id]
  exact (Category.comp_id _).trans (DerivedCategory.Qh.map_id K)

private instance identity_unit_isIso
    (C : Type*) [Category C] [Abelian C] [HasDerivedCategory C] :
    IsIso (identity_unit C) := by
  dsimp only [identity_unit]
  infer_instance

private instance identity_isRightDerived
    (C : Type*) [Category C] [Abelian C] [HasDerivedCategory C] :
    (𝟭 (DerivedCategory C)).IsRightDerivedFunctor (identity_unit C)
      (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)) :=
  Functor.isRightDerivedFunctor_of_inverts _ _ (asIso (identity_unit C)).symm

@[irreducible] private noncomputable def identity_iso
    (C : Type*) [Category C] [Abelian C] [HasDerivedCategory C]
    [HasKInjectiveResolutions C] :
    (𝟭 C).rightDerivedFunctor ≅ 𝟭 (DerivedCategory C) :=
  Functor.rightDerivedUnique (𝟭 C).rightDerivedFunctor (𝟭 (DerivedCategory C))
    (𝟭 C).rightDerivedFunctorUnit (identity_unit C)
    (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))

private theorem identity_iso_fac
    (C : Type*) [Category C] [Abelian C] [HasDerivedCategory C]
    [HasKInjectiveResolutions C] (K : HomotopyCategory C (ComplexShape.up ℤ)) :
    (𝟭 C).rightDerivedFunctorUnit.app K ≫
      (identity_iso C).hom.app (DerivedCategory.Qh.obj K) = 𝟙 _ := by
  have h : (𝟭 C).rightDerivedFunctorUnit ≫
      Functor.whiskerLeft DerivedCategory.Qh (identity_iso C).hom = identity_unit C := by
    simp [identity_iso]
  simpa only [NatTrans.comp_app, Functor.whiskerLeft_app, identity_unit_app] using
    NatTrans.congr_app h K

@[irreducible] private noncomputable def derived_identity_iso
    {C : Type*} [Category C] [Abelian C] [dC : HasDerivedCategory C]
    [HasKInjectiveResolutions C] (U : C ⥤ C) [U.Additive] (h : U = 𝟭 C) :
    U.rightDerivedFunctor ≅ 𝟭 (DerivedCategory C) :=
  Functor.rightDerivedFunctorNatIso (eqToIso h) ≪≫ identity_iso C

private theorem derived_identity_iso_id
    (C : Type*) [Category C] [Abelian C] [HasDerivedCategory C]
    [HasKInjectiveResolutions C] :
    derived_identity_iso (𝟭 C) rfl = identity_iso C := by
  apply Iso.ext
  simp [derived_identity_iso, Functor.rightDerivedFunctorNatIso,
    Functor.rightDerivedFunctorNatTrans]

private theorem derived_unit_left
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [dC : HasDerivedCategory C] [dD : HasDerivedCategory D]
    [HasKInjectiveResolutions C] (F : C ⥤ D) [F.Additive]
    (U : C ⥤ C) [U.Additive] (hU : U = 𝟭 C)
    (a : U.rightDerivedFunctor ⋙ F.rightDerivedFunctor ≅ F.rightDerivedFunctor)
    (ha : ∀ K : HomotopyCategory C (ComplexShape.up ℤ),
      HEq (F.rightDerivedFunctorUnit.app K ≫ a.inv.app (DerivedCategory.Qh.obj K))
        (F.rightDerivedFunctorUnit.app ((U.mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫
          F.rightDerivedFunctor.map (U.rightDerivedFunctorUnit.app K))) :
    a.hom = Functor.whiskerRight (derived_identity_iso U hU).hom
      F.rightDerivedFunctor ≫ F.rightDerivedFunctor.leftUnitor.hom := by
  subst U
  rw [derived_identity_iso_id]
  change a.hom = Functor.whiskerRight (identity_iso C).hom
    F.rightDerivedFunctor ≫ F.rightDerivedFunctor.leftUnitor.hom
  let b := Functor.isoWhiskerRight (identity_iso C)
    F.rightDerivedFunctor ≪≫ F.rightDerivedFunctor.leftUnitor
  have h : a.inv ≫ b.hom = 𝟙 F.rightDerivedFunctor := by
    apply F.rightDerivedFunctor.rightDerived_ext F.rightDerivedFunctorUnit
      (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))
    ext K
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, NatTrans.id_app]
    rw [← Category.assoc, eq_of_heq (ha K)]
    dsimp only [b, Iso.trans_hom, Functor.isoWhiskerRight_hom, NatTrans.comp_app,
      Functor.whiskerRight_app, Functor.leftUnitor_hom_app]
    erw [Category.comp_id, Category.comp_id, Category.assoc,
      ← F.rightDerivedFunctor.map_comp, identity_iso_fac,
      F.rightDerivedFunctor.map_id, Category.comp_id]
    rfl
  calc
    a.hom = a.hom ≫ (a.inv ≫ b.hom) := by rw [h, Category.comp_id]
    _ = b.hom := by rw [← Category.assoc, a.hom_inv_id, Category.id_comp]

private theorem derived_unit_right
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [dC : HasDerivedCategory C] [dD : HasDerivedCategory D]
    [HasKInjectiveResolutions C] [HasKInjectiveResolutions D] (F : C ⥤ D) [F.Additive]
    (U : D ⥤ D) [U.Additive] (hU : U = 𝟭 D)
    (a : F.rightDerivedFunctor ⋙ U.rightDerivedFunctor ≅ F.rightDerivedFunctor)
    (ha : ∀ K : HomotopyCategory C (ComplexShape.up ℤ),
      HEq (F.rightDerivedFunctorUnit.app K ≫ a.inv.app (DerivedCategory.Qh.obj K))
        (U.rightDerivedFunctorUnit.app
            ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫
          U.rightDerivedFunctor.map (F.rightDerivedFunctorUnit.app K))) :
    a.hom = Functor.whiskerLeft F.rightDerivedFunctor
      (derived_identity_iso U hU).hom ≫ F.rightDerivedFunctor.rightUnitor.hom := by
  subst U
  rw [derived_identity_iso_id]
  change a.hom = Functor.whiskerLeft F.rightDerivedFunctor
    (identity_iso D).hom ≫ F.rightDerivedFunctor.rightUnitor.hom
  let b := Functor.isoWhiskerLeft F.rightDerivedFunctor
    (identity_iso D) ≪≫ F.rightDerivedFunctor.rightUnitor
  have h : a.inv ≫ b.hom = 𝟙 F.rightDerivedFunctor := by
    apply F.rightDerivedFunctor.rightDerived_ext F.rightDerivedFunctorUnit
      (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))
    ext K
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, NatTrans.id_app]
    rw [← Category.assoc, eq_of_heq (ha K)]
    dsimp only [b, Iso.trans_hom, Functor.isoWhiskerLeft_hom, NatTrans.comp_app,
      Functor.whiskerLeft_app, Functor.rightUnitor_hom_app]
    erw [Category.comp_id, Category.comp_id, Category.assoc,
      (identity_iso D).hom.naturality,
      ← Category.assoc, identity_iso_fac, Category.id_comp]
    rfl
  calc
    a.hom = a.hom ≫ (a.inv ≫ b.hom) := by rw [h, Category.comp_id]
    _ = b.hom := by rw [← Category.assoc, a.hom_inv_id, Category.id_comp]

private theorem derived_unit_left_transport
    {M C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [dC : HasDerivedCategory C] [dD : HasDerivedCategory D] [HasKInjectiveResolutions C]
    (F : M → C ⥤ D) [hF : ∀ m, (F m).Additive]
    (f g : M) (h : g = f) (U : C ⥤ C) [U.Additive] (hU : U = 𝟭 C)
    (a : U.rightDerivedFunctor ⋙ (F f).rightDerivedFunctor ≅ (F g).rightDerivedFunctor)
    (ha : ∀ K : HomotopyCategory C (ComplexShape.up ℤ),
      HEq ((F g).rightDerivedFunctorUnit.app K ≫ a.inv.app (DerivedCategory.Qh.obj K))
        ((F f).rightDerivedFunctorUnit.app
            ((U.mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫
          (F f).rightDerivedFunctor.map (U.rightDerivedFunctorUnit.app K)))
    (E : DerivedCategory C) :
    a.hom.app E ≫ eqToHom (congrArg (fun m => (F m).rightDerivedFunctor.obj E) h) =
      (F f).rightDerivedFunctor.map ((derived_identity_iso U hU).hom.app E) := by
  subst g
  have hh := NatTrans.congr_app (derived_unit_left (F f) U hU a ha) E
  dsimp only [NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.leftUnitor_hom_app] at hh
  exact (Category.comp_id _).trans (hh.trans (Category.comp_id _))

private theorem derived_unit_right_transport
    {M C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [dC : HasDerivedCategory C] [dD : HasDerivedCategory D]
    [HasKInjectiveResolutions C] [HasKInjectiveResolutions D]
    (F : M → C ⥤ D) [hF : ∀ m, (F m).Additive]
    (f g : M) (h : g = f) (U : D ⥤ D) [U.Additive] (hU : U = 𝟭 D)
    (a : (F f).rightDerivedFunctor ⋙ U.rightDerivedFunctor ≅ (F g).rightDerivedFunctor)
    (ha : ∀ K : HomotopyCategory C (ComplexShape.up ℤ),
      HEq ((F g).rightDerivedFunctorUnit.app K ≫ a.inv.app (DerivedCategory.Qh.obj K))
        (U.rightDerivedFunctorUnit.app
            (((F f).mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫
          U.rightDerivedFunctor.map ((F f).rightDerivedFunctorUnit.app K)))
    (E : DerivedCategory C) :
    a.hom.app E ≫ eqToHom (congrArg (fun m => (F m).rightDerivedFunctor.obj E) h) =
      (derived_identity_iso U hU).hom.app ((F f).rightDerivedFunctor.obj E) := by
  subst g
  have hh := NatTrans.congr_app (derived_unit_right (F f) U hU a ha) E
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.rightUnitor_hom_app] at hh
  exact (Category.comp_id _).trans (hh.trans (Category.comp_id _))

private theorem derived_unit_laws
    {S : Type*} [Category S] (C : S → Type*)
    [cat : ∀ X, Category (C X)] [ab : ∀ X, Abelian (C X)]
    [d : ∀ X, HasDerivedCategory (C X)] [ki : ∀ X, HasKInjectiveResolutions (C X)]
    (F : ∀ {X Y : S}, (X ⟶ Y) → C X ⥤ C Y)
    [hF : ∀ {X Y : S} (f : X ⟶ Y), (F f).Additive]
    (hi : ∀ X, F (𝟙 X) = 𝟭 (C X))
    (c : ∀ {X Y Z : S} (f : X ⟶ Y) (g : Y ⟶ Z),
      (F f).rightDerivedFunctor ⋙ (F g).rightDerivedFunctor ≅
        (F (f ≫ g)).rightDerivedFunctor)
    (hc : ∀ {X Y Z : S} (f : X ⟶ Y) (g : Y ⟶ Z)
        (K : HomotopyCategory (C X) (ComplexShape.up ℤ)),
      HEq ((F (f ≫ g)).rightDerivedFunctorUnit.app K ≫
          (c f g).inv.app (DerivedCategory.Qh.obj K))
        ((F g).rightDerivedFunctorUnit.app
            (((F f).mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫
          (F g).rightDerivedFunctor.map ((F f).rightDerivedFunctorUnit.app K))) :
    ∃ i : ∀ X, (F (𝟙 X)).rightDerivedFunctor ≅ 𝟭 (DerivedCategory (C X)),
      (∀ {X Y : S} (f : X ⟶ Y) (E : DerivedCategory (C X)),
        (c (𝟙 X) f).hom.app E ≫
            eqToHom (congrArg (fun k : X ⟶ Y => (F k).rightDerivedFunctor.obj E)
              (Category.id_comp f)) =
          (F f).rightDerivedFunctor.map ((i X).hom.app E)) ∧
      (∀ {X Y : S} (f : X ⟶ Y) (E : DerivedCategory (C X)),
        (c f (𝟙 Y)).hom.app E ≫
            eqToHom (congrArg (fun k : X ⟶ Y => (F k).rightDerivedFunctor.obj E)
              (Category.comp_id f)) =
          (i Y).hom.app ((F f).rightDerivedFunctor.obj E)) := by
  refine ⟨fun X => derived_identity_iso (F (𝟙 X)) (hi X), ?_, ?_⟩
  · intro X Y f E
    exact derived_unit_left_transport (dC := d X) (dD := d Y)
      (fun k : X ⟶ Y => F k) (hF := fun k => hF k)
      f (𝟙 X ≫ f) (Category.id_comp f) (F (𝟙 X)) (hi X)
      (c (𝟙 X) f) (hc (𝟙 X) f) E
  · intro X Y f E
    exact derived_unit_right_transport (dC := d X) (dD := d Y)
      (fun k : X ⟶ Y => F k) (hF := fun k => hF k)
      f (f ≫ 𝟙 Y) (Category.comp_id f) (F (𝟙 Y)) (hi Y)
      (c f (𝟙 Y)) (hc f (𝟙 Y)) E

set_option maxHeartbeats 600000 in
-- Specializing the dependent unit equations for the sheaf pushforward family.
/-- The two unit laws for any direct-image comparisons characterized by the right-derived
unit equation, on the whole unbounded derived categories.
Source: Stacks Project, Cohomology, Tag 0D5T, with identity derived functor uniqueness.
(blueprint: lem-pc-derived-direct-image-composition-unit-laws).

Proof: underived direct image for an identity is canonically the identity functor,
with the sectionwise identity as its unitor. Derive this identification. Since the identity
functor is exact, its derived functor is the identity on the localization; uniqueness of
right derived functors gives i X, characterized by the derived-unit equation with this
underived unitor. The hypothesis hc transports the right-derived universal property of
the composite morphism to the composite derived functors, with the pasted unit.
For c (id X) f, substitute the defining equation of i X into that pasted unit and use
naturality of the derived unit of f. The result is the derived unit of f composed with
the underived left unitor. For c f (id Y), substitute the equation for i Y; the result
is the same with the right unitor. In both cases the other side of the claimed law has
exactly this factorization. Uniqueness of morphisms out of the right derived functor
therefore equates the natural transformations. Evaluating at E gives the displayed
equalities, with eqToHom accounting for id_comp and comp_id. -/
theorem derivedDirectImageComposition_unit_laws
    [d : ∀ X : Scheme.{u}, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (c : ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z),
      schemeDerivedDirectImage f ⋙ schemeDerivedDirectImage g ≅
        schemeDerivedDirectImage (f ≫ g))
    (hc : ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
        (K : HomotopyCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace))
          (ComplexShape.up ℤ)),
      (RingedSpace.moduleDirectImage (f ≫ g).toLRSHom.toShHom).rightDerivedFunctorUnit.app K ≫
          (c f g).inv.app (DerivedCategory.Qh.obj K) =
        (RingedSpace.moduleDirectImage g.toLRSHom.toShHom).rightDerivedFunctorUnit.app
            (((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).mapHomotopyCategory
              (ComplexShape.up ℤ)).obj K) ≫
          (schemeDerivedDirectImage g).map
            ((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).rightDerivedFunctorUnit.app K)) :
    ∃ i : ∀ X : Scheme.{u}, schemeDerivedDirectImage (𝟙 X) ≅ 𝟭 (schemeDerivedCategory X),
      (∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (E : schemeDerivedCategory X),
        (c (𝟙 X) f).hom.app E ≫
            eqToHom (congrArg (fun k : X ⟶ Y => (schemeDerivedDirectImage k).obj E)
              (Category.id_comp f)) =
          (schemeDerivedDirectImage f).map ((i X).hom.app E)) ∧
      (∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (E : schemeDerivedCategory X),
        (c f (𝟙 Y)).hom.app E ≫
            eqToHom (congrArg (fun k : X ⟶ Y => (schemeDerivedDirectImage k).obj E)
              (Category.comp_id f)) =
          (i Y).hom.app ((schemeDerivedDirectImage f).obj E)) := by
  exact derived_unit_laws (S := Scheme.{u})
    (C := fun X : Scheme.{u} => SheafOfModules.{u} (moduleRings X.toRingedSpace))
    (d := d)
    (fun {X Y : Scheme.{u}} (f : X ⟶ Y) =>
      RingedSpace.moduleDirectImage f.toLRSHom.toShHom)
    (hF := fun {X Y : Scheme.{u}} (f : X ⟶ Y) =>
      RingedSpace.moduleDirectImage_additive f.toLRSHom.toShHom)
    moduleDirectImage_id c (fun f g K => heq_of_eq (hc f g K))

end AlgebraicGeometry
