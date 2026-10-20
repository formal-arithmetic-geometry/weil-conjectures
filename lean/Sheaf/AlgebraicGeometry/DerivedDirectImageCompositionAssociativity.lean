/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A3
-/
module

public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage

/-!
# Coherence of canonical unbounded derived direct images

Source: Stacks Project, Cohomology, Tag 0D5T and its derived universal property.
-/

@[expose] public section

universe u w

open CategoryTheory

set_option autoImplicit false

namespace AlgebraicGeometry

private theorem ringedDirectImage_comp {X Y Z : RingedSpace.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    RingedSpace.moduleDirectImage (f ≫ g) =
      RingedSpace.moduleDirectImage f ⋙ RingedSpace.moduleDirectImage g := rfl

-- Use the universal-property API without unfolding the chosen localization data.
attribute [local irreducible] CategoryTheory.Functor.rightDerivedFunctor
  CategoryTheory.Functor.rightDerivedFunctorUnit

private theorem map_pasted_square
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {A B B' E : C} {a : A ⟶ B} {b : B ⟶ E} {a' : A ⟶ B'} {b' : B' ⟶ E}
    (h : a ≫ b = a' ≫ b') : F.map a ≫ F.map b = F.map a' ≫ F.map b' := by
  simp only [← F.map_comp, h]

private theorem pasted_comparisons
    {C : Type*} [Category C] {A B B' D E F G H I : C}
    {u : A ⟶ B} {u' : A ⟶ B'} {t : B ⟶ B'}
    {x : B' ⟶ D} {y : D ⟶ E} {c : B ⟶ F} {d : F ⟶ E}
    {α : A ⟶ G} {β : G ⟶ D} {l : G ⟶ H} {μ : H ⟶ E}
    {δ : A ⟶ I} {ε : I ⟶ F} {ν : I ⟶ H}
    (h₁ : u' ≫ x = α ≫ β) (h₂ : β ≫ y = l ≫ μ)
    (h₃ : u ≫ c = δ ≫ ε) (h₄ : ε ≫ d = ν ≫ μ)
    (h₅ : δ ≫ ν = α ≫ l) (ht : u ≫ t = u') :
    u ≫ (t ≫ x) ≫ y = u ≫ (c ≫ d) ≫ 𝟙 E := by
  calc
    _ = (u' ≫ x) ≫ y := by simp only [← Category.assoc, ht]
    _ = α ≫ (l ≫ μ) := by rw [h₁, Category.assoc, h₂]
    _ = (δ ≫ ν) ≫ μ := by rw [← Category.assoc, h₅]
    _ = (δ ≫ ε) ≫ d := by rw [Category.assoc, ← h₄, ← Category.assoc]
    _ = _ := by rw [← h₃]; simp only [Category.assoc, Category.comp_id]

private theorem derived_pasted_comparisons
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [dA : HasDerivedCategory A] [dB : HasDerivedCategory B]
    [dC : HasDerivedCategory C] [dD : HasDerivedCategory D]
    [CategoryTheory.Abelian.HasKInjectiveResolutions A]
    [CategoryTheory.Abelian.HasKInjectiveResolutions B]
    [CategoryTheory.Abelian.HasKInjectiveResolutions C]
    (F : A ⥤ B) (G : B ⥤ C) (H : C ⥤ D)
    (FG : A ⥤ C) (GH : B ⥤ D) (T₁ T₂ : A ⥤ D)
    [F.Additive] [G.Additive] [H.Additive] [FG.Additive] [GH.Additive]
    [T₁.Additive] [T₂.Additive]
    (hFG : FG = F ⋙ G) (hGH : GH = G ⋙ H)
    (hT₁ : T₁ = FG ⋙ H) (hT₂ : T₂ = F ⋙ GH)
    (c₁ : F.rightDerivedFunctor ⋙ G.rightDerivedFunctor ≅ FG.rightDerivedFunctor)
    (c₂ : G.rightDerivedFunctor ⋙ H.rightDerivedFunctor ≅ GH.rightDerivedFunctor)
    (c₃ : FG.rightDerivedFunctor ⋙ H.rightDerivedFunctor ≅ T₁.rightDerivedFunctor)
    (c₄ : F.rightDerivedFunctor ⋙ GH.rightDerivedFunctor ≅ T₂.rightDerivedFunctor)
    (t : T₁.rightDerivedFunctor ≅ T₂.rightDerivedFunctor)
    (hc₁ : ∀ K : HomotopyCategory A (ComplexShape.up ℤ),
      HEq (FG.rightDerivedFunctorUnit.app K ≫ c₁.inv.app (DerivedCategory.Qh.obj K))
        (G.rightDerivedFunctorUnit.app ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫
          G.rightDerivedFunctor.map (F.rightDerivedFunctorUnit.app K)))
    (hc₂ : ∀ K : HomotopyCategory B (ComplexShape.up ℤ),
      HEq (GH.rightDerivedFunctorUnit.app K ≫ c₂.inv.app (DerivedCategory.Qh.obj K))
        (H.rightDerivedFunctorUnit.app ((G.mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫
          H.rightDerivedFunctor.map (G.rightDerivedFunctorUnit.app K)))
    (hc₃ : ∀ K : HomotopyCategory A (ComplexShape.up ℤ),
      HEq (T₁.rightDerivedFunctorUnit.app K ≫ c₃.inv.app (DerivedCategory.Qh.obj K))
        (H.rightDerivedFunctorUnit.app ((FG.mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫
          H.rightDerivedFunctor.map (FG.rightDerivedFunctorUnit.app K)))
    (hc₄ : ∀ K : HomotopyCategory A (ComplexShape.up ℤ),
      HEq (T₂.rightDerivedFunctorUnit.app K ≫ c₄.inv.app (DerivedCategory.Qh.obj K))
        (GH.rightDerivedFunctorUnit.app ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫
          GH.rightDerivedFunctor.map (F.rightDerivedFunctorUnit.app K)))
    (ht : ∀ K : HomotopyCategory A (ComplexShape.up ℤ),
      HEq (T₂.rightDerivedFunctorUnit.app K ≫ t.inv.app (DerivedCategory.Qh.obj K))
        (T₁.rightDerivedFunctorUnit.app K))
    (E : DerivedCategory A) :
    H.rightDerivedFunctor.map (c₁.hom.app E) ≫ c₃.hom.app E ≫ t.hom.app E =
      c₂.hom.app (F.rightDerivedFunctor.obj E) ≫ c₄.hom.app E := by
  subst FG GH T₁ T₂
  let a := Functor.isoWhiskerRight c₁ H.rightDerivedFunctor ≪≫ c₃ ≪≫ t
  let b := Functor.associator F.rightDerivedFunctor G.rightDerivedFunctor H.rightDerivedFunctor ≪≫
    Functor.isoWhiskerLeft F.rightDerivedFunctor c₂ ≪≫ c₄
  have hab : a.inv = b.inv := by
    apply Functor.rightDerived_ext (F ⋙ G ⋙ H).rightDerivedFunctor
      (F ⋙ G ⋙ H).rightDerivedFunctorUnit
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))
    ext K
    simp only [a, b, Iso.trans_inv, NatTrans.comp_app, Functor.isoWhiskerRight_inv,
      Functor.isoWhiskerLeft_inv, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Functor.associator_inv_app]
    exact pasted_comparisons (C := DerivedCategory D)
      (t := t.inv.app (DerivedCategory.Qh.obj K))
      (eq_of_heq (hc₃ K))
      (map_pasted_square H.rightDerivedFunctor (eq_of_heq (hc₁ K)))
      (eq_of_heq (hc₄ K))
      (c₂.inv.naturality (F.rightDerivedFunctorUnit.app K))
      (eq_of_heq (hc₂ ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj K)))
      (eq_of_heq (ht K))
  have he := congrArg (fun v ↦ a.hom ≫ v ≫ b.hom) hab
  have he' : a.hom = b.hom := by simpa using he.symm
  simpa [a, b] using NatTrans.congr_app he' E

set_option maxHeartbeats 400000 in
-- The sectionwise composite source is definitionally the iterated direct image.
private theorem directImageNormalization_heq
    [d : ∀ X : Scheme.{u}, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    {X Y Z : Scheme.{u}}
    [kX : CategoryTheory.Abelian.HasKInjectiveResolutions
      (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [kY : CategoryTheory.Abelian.HasKInjectiveResolutions
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (cmp : (RingedSpace.moduleDirectImage f.toLRSHom.toShHom).rightDerivedFunctor ⋙
        (RingedSpace.moduleDirectImage g.toLRSHom.toShHom).rightDerivedFunctor ≅
      (RingedSpace.moduleDirectImage (f ≫ g).toLRSHom.toShHom).rightDerivedFunctor)
    (hc : ∀ K : HomotopyCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace))
        (ComplexShape.up ℤ),
      (RingedSpace.moduleDirectImage (f ≫ g).toLRSHom.toShHom).rightDerivedFunctorUnit.app K ≫
          cmp.inv.app (DerivedCategory.Qh.obj K) =
        (RingedSpace.moduleDirectImage g.toLRSHom.toShHom).rightDerivedFunctorUnit.app
            (((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).mapHomotopyCategory
              (ComplexShape.up ℤ)).obj K) ≫
          ((RingedSpace.moduleDirectImage g.toLRSHom.toShHom).rightDerivedFunctor).map
            ((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).rightDerivedFunctorUnit.app K))
    (K : HomotopyCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace))
      (ComplexShape.up ℤ)) :
    HEq ((RingedSpace.moduleDirectImage (f ≫ g).toLRSHom.toShHom).rightDerivedFunctorUnit.app
        K ≫ cmp.inv.app (DerivedCategory.Qh.obj K))
      ((RingedSpace.moduleDirectImage g.toLRSHom.toShHom).rightDerivedFunctorUnit.app
          (((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).mapHomotopyCategory
            (ComplexShape.up ℤ)).obj K) ≫
        ((RingedSpace.moduleDirectImage g.toLRSHom.toShHom).rightDerivedFunctor).map
          ((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).rightDerivedFunctorUnit.app K)) := by
  have hh := heq_of_eq (hc K)
  exact hh

private theorem directImageUnit_congr
    [d : ∀ X : Scheme.{u}, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    {X Y : Scheme.{u}}
    [kX : CategoryTheory.Abelian.HasKInjectiveResolutions
      (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (f g : X ⟶ Y) (e : f = g)
    (K : HomotopyCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace))
      (ComplexShape.up ℤ)) :
    HEq ((RingedSpace.moduleDirectImage g.toLRSHom.toShHom).rightDerivedFunctorUnit.app K ≫
        (eqToIso (congrArg (fun k : X ⟶ Y ↦
          (RingedSpace.moduleDirectImage k.toLRSHom.toShHom).rightDerivedFunctor) e)).inv.app
          (DerivedCategory.Qh.obj K))
      ((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).rightDerivedFunctorUnit.app K) := by
  subst g
  simp

set_option maxHeartbeats 800000 in
-- Comparing the pasted units checks sectionwise direct-image composition.
/-- Associativity for direct-image comparisons characterized by the right-derived unit,
on the whole unbounded derived categories.
Source: Stacks Project, Cohomology, Tag 0D5T, coherence by derived uniqueness.
(blueprint: lem-pc-derived-direct-image-composition-associativity).

Proof: take inverses of the two composite isomorphisms from Rf Rg Rh to R(hgf).
Precompose their natural transformations with the derived unit for the triple composite.
Apply hc twice on each side. Naturality of the derived unit for h moves the unit for f
past the middle comparison. Functoriality and associativity of composition then make
both results the same triple pasted unit: the unit for h at g applied to f applied to K,
followed by Rh of the unit for g at f applied to K, followed by Rh Rg of the unit for f
at K. The underived direct-image associator agrees in the two paths, since its maps on
sections are the canonical scalar-restriction and inverse-image identifications.
Uniqueness of transformations out of the right derived functor of hgf gives equality of
the inverse transformations. Inverting, then evaluating at E, proves the displayed
formula; eqToHom records the equality between the two composite scheme morphisms. -/
theorem derivedDirectImageComposition_associativity
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
    ∀ {W X Y Z : Scheme.{u}} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z)
      (E : schemeDerivedCategory W),
      (schemeDerivedDirectImage h).map ((c f g).hom.app E) ≫
          (c (f ≫ g) h).hom.app E ≫
          eqToHom (congrArg (fun k : W ⟶ Z => (schemeDerivedDirectImage k).obj E)
            (Category.assoc f g h)) =
        (c g h).hom.app ((schemeDerivedDirectImage f).obj E) ≫
          (c f (g ≫ h)).hom.app E := by
  intro W X Y Z f g h E
  let := d W
  let := d X
  let := d Y
  let := d Z
  let t := eqToIso (congrArg (fun k : W ⟶ Z ↦ schemeDerivedDirectImage k)
    (Category.assoc f g h))
  have he := derived_pasted_comparisons
    (A := SheafOfModules.{u} (moduleRings W.toRingedSpace))
    (B := SheafOfModules.{u} (moduleRings X.toRingedSpace))
    (C := SheafOfModules.{u} (moduleRings Y.toRingedSpace))
    (D := SheafOfModules.{u} (moduleRings Z.toRingedSpace))
    (dA := d W) (dB := d X) (dC := d Y) (dD := d Z)
    (RingedSpace.moduleDirectImage f.toLRSHom.toShHom)
    (RingedSpace.moduleDirectImage g.toLRSHom.toShHom)
    (RingedSpace.moduleDirectImage h.toLRSHom.toShHom)
    (RingedSpace.moduleDirectImage (f ≫ g).toLRSHom.toShHom)
    (RingedSpace.moduleDirectImage (g ≫ h).toLRSHom.toShHom)
    (RingedSpace.moduleDirectImage ((f ≫ g) ≫ h).toLRSHom.toShHom)
    (RingedSpace.moduleDirectImage (f ≫ g ≫ h).toLRSHom.toShHom)
    (ringedDirectImage_comp f.toLRSHom.toShHom g.toLRSHom.toShHom)
    (ringedDirectImage_comp g.toLRSHom.toShHom h.toLRSHom.toShHom)
    (ringedDirectImage_comp (f ≫ g).toLRSHom.toShHom h.toLRSHom.toShHom)
    (ringedDirectImage_comp f.toLRSHom.toShHom (g ≫ h).toLRSHom.toShHom)
    (c f g) (c g h) (c (f ≫ g) h) (c f (g ≫ h)) t
    (directImageNormalization_heq f g (c f g) (hc f g))
    (directImageNormalization_heq g h (c g h) (hc g h))
    (directImageNormalization_heq (f ≫ g) h (c (f ≫ g) h) (hc (f ≫ g) h))
    (directImageNormalization_heq f (g ≫ h) (c f (g ≫ h)) (hc f (g ≫ h)))
    (directImageUnit_congr ((f ≫ g) ≫ h) (f ≫ g ≫ h) (Category.assoc f g h)) E
  simpa only [t, eqToIso, eqToHom_app] using he

end AlgebraicGeometry
