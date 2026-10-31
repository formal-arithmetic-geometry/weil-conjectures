/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ShriekNormalizedTransitionData

/-! # Cocycle of normalized scalar transitions -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option backward.defeqAttrib.useBackward false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures
namespace AlgebraicGeometry.ProEtale.SpShriekTransition
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
attribute [local irreducible] scalarCoordinates quotientMap
  Functor.mapDerivedCategory Functor.rightDerivedFunctor HasDerivedCategory.standard
  Padic Padic.coefficientExtensionIntegers scalarExtensionFunctor SemilinearSections.reduction
attribute [local implicit_reducible] SemilinearSections.hasDerived
  SemilinearSections.moduleAbelian
attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem transport_cocycle
    {A B C : Type*} [categoryA : Category A] [categoryB : Category B]
    [categoryC : Category C]
    {S S' : A ⥤ B} {T T' : B ⥤ C} {R R' : A ⥤ C}
    (s : S ≅ S') (t : T ≅ T') (r : R ≅ R') (a : S ⋙ T ≅ R)
    {K : A} {L : B} {M : C} (f : S.obj K ⟶ L) (g : T.obj L ⟶ M)
    (h : R.obj K ⟶ M) (w : T.map f ≫ g = a.hom.app K ≫ h) :
    T'.map (coordinateReduction s f) ≫ coordinateReduction t g =
      (coordinateAssociator s t r a).hom.app K ≫ coordinateReduction r h := by
  simp only [coordinateReduction, coordinateAssociator,
    Functor.map_comp, Category.assoc, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom, Iso.symm_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app]
  rw [t.inv.naturality_assoc, w]
  simp only [Iso.hom_inv_id_app_assoc]

private abbrev nativeHom {A : Type*} [categoryA : Category A] (X Y : A) :=
  @Quiver.Hom A (@ReflQuiver.toQuiver A (@catToReflQuiver A categoryA)) X Y

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem transport_cocycle_values
    {A B C : Type*} [categoryA : Category A] [categoryB : Category B]
    [categoryC : Category C]
    (S' : A ⥤ B) (T' : B ⥤ C) (R' : A ⥤ C)
    {S : A ⥤ B} {T : B ⥤ C} {R : A ⥤ C}
    {K : A} {L : B} {M : C}
    (s : S ≅ S') (t : T ≅ T') (r : R ≅ R') (a : S ⋙ T ≅ R)
    (f : nativeHom (S.obj K) L) (g : nativeHom (T.obj L) M)
    (h : nativeHom (R.obj K) M)
    (f' : S'.obj K ⟶ L) (g' : T'.obj L ⟶ M) (h' : R'.obj K ⟶ M)
    (a' : S' ⋙ T' ≅ R')
    (ef : f' = coordinateReduction s f) (eg : g' = coordinateReduction t g)
    (eh : h' = coordinateReduction r h) (ea : a' = coordinateAssociator s t r a)
    (w : T.map f ≫ g = a.hom.app K ≫ h) :
    T'.map f' ≫ g' = a'.hom.app K ≫ h' := by
  rw [ef, eg, eh, ea]
  exact transport_cocycle s t r a f g h w

attribute [-instance] CategoryTheory.catToReflQuiver in
/-- The normalized scalar reductions satisfy the canonical coefficient cocycle.
Source: Zheng Construction 4.1; transport of the published reduction cocycle through
adjunction-unique scalar coordinates. The proof expands the three coordinate changes,
uses inverse-coordinate naturality, applies the original reduction cocycle, and cancels
the composite coordinate isomorphism. This is an independent derived-category
calculation and is kept separate from the proper and open geometric transition squares.
(blueprint: lem-sp-normalized-transition-cocycle). -/
theorem rho_cocycle (b : SpTowerShriek.Base l E) (T : Scheme.{u})
    {r m n : ℕ} (h : r ≤ m) (k : m ≤ n) (M : SpTowerShriek.D l E T) :
    (scalarExtensionFunctor (quotientMap l E h) T).map (rho l E b T k M) ≫
        rho l E b T h M =
      (alpha l E b T h k).hom.app ((SpTowerShriek.Ev l E T n).obj M) ≫
        rho l E b T (h.trans k) M := by
  exact transport_cocycle_values
    (A := proEtaleDerivedCategory T (SpTowerShriek.R l E n))
    (B := proEtaleDerivedCategory T (SpTowerShriek.R l E m))
    (C := proEtaleDerivedCategory T (SpTowerShriek.R l E r))
    (categoryA := @instCategoryDerivedCategory _ _ _ (HasDerivedCategory.standard _))
    (categoryB := @instCategoryDerivedCategory _ _ _ (HasDerivedCategory.standard _))
    (categoryC := @instCategoryDerivedCategory _ _ _ (HasDerivedCategory.standard _))
    (scalarExtensionFunctor (quotientMap l E k) T)
    (scalarExtensionFunctor (quotientMap l E h) T)
    (scalarExtensionFunctor (quotientMap l E (h.trans k)) T)
    (K := (SpTowerShriek.Ev l E T n).obj M)
    (L := (SpTowerShriek.Ev l E T m).obj M)
    (M := (SpTowerShriek.Ev l E T r).obj M)
    (scalarCoordinates l E b T k) (scalarCoordinates l E b T h)
    (scalarCoordinates l E b T (h.trans k)) ((b.calculus T).scalarComposition h k)
    (SemilinearSections.reduction (ProEt.topology T) (SpTowerShriek.B l E T)
      (SpTowerShriek.tau l E T) k ((b.calculus T).scalar k) M)
    (SemilinearSections.reduction (ProEt.topology T) (SpTowerShriek.B l E T)
      (SpTowerShriek.tau l E T) h ((b.calculus T).scalar h) M)
    (SemilinearSections.reduction (ProEt.topology T) (SpTowerShriek.B l E T)
      (SpTowerShriek.tau l E T) (h.trans k) ((b.calculus T).scalar (h.trans k)) M)
    (rho l E b T k M) (rho l E b T h M) (rho l E b T (h.trans k) M)
    (alpha l E b T h k) rfl rfl rfl rfl
    ((b.calculus T).reduction_cocycle h k M)

end AlgebraicGeometry.ProEtale.SpShriekTransition
