/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.GlobalHomAdjunctionIso
public import WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedDirectImageComposition
import WeilConjectures.AlgebraicGeometry.DerivedPullbackCompositionMateUnit

/-! # Normalized direct-image square as a pullback mate
Source: Stacks Project, cohomology.tex, Tags 08HY, 0D5T and 0D5W.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u w
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
namespace AlgebraicGeometry
variable [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
/-- The fixed direct-image composition comparison, typed on schemes (Stacks, Tag 0D5T). -/
noncomputable def schemeNormalizedDirectImageCompIso
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    schemeDerivedDirectImage f ⋙ schemeDerivedDirectImage g ≅
      schemeDerivedDirectImage (f ≫ g) :=
  Classical.choose (RingedSpace.exists_derivedModuleDirectImageComposition
    f.toLRSHom.toShHom g.toLRSHom.toShHom)

-- Checking canonical comparison choices expands derived-functor and sheaf instances.
/-- The mate of the fixed pullback square is the normalized direct-image square
(Stacks, Tags 08HY and 0D5T). -/
theorem derivedDirectImage_square_mate
    {X Y X' Y' : Scheme.{u}}
    (f : X ⟶ Y) (f' : X' ⟶ Y') (g : Y' ⟶ Y) (gX : X' ⟶ X)
    (h : gX ≫ f = f' ≫ g) :
    let a := fun {A D : Scheme.{u}} (t : A ⟶ D) ↦ schemeHomPullbackAdjunction t
    let p := @Classical.choose _ _ (Classical.choose_spec (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition.{u, w})))
    let k := p f' g ≪≫
      eqToIso (congrArg (fun t ↦ derivedPullback t) h.symm) ≪≫ (p gX f).symm
    let e₁ : schemeDerivedDirectImage gX ⋙ schemeDerivedDirectImage f ≅
        schemeDerivedDirectImage (gX ≫ f) :=
      schemeNormalizedDirectImageCompIso gX f
    let e₂ : schemeDerivedDirectImage f' ⋙ schemeDerivedDirectImage g ≅
        schemeDerivedDirectImage (f' ≫ g) :=
      schemeNormalizedDirectImageCompIso f' g
    conjugateEquiv ((a f).comp (a gX)) ((a g).comp (a f')) k.hom =
      e₁.hom ≫ eqToHom (congrArg (fun t ↦ schemeDerivedDirectImage t) h) ≫ e₂.inv := by
  let a := fun {A D : Scheme.{u}} (t : A ⟶ D) ↦ schemeHomPullbackAdjunction t
  let p : ∀ {A B C : Scheme.{u}} (s : A ⟶ B) (t : B ⟶ C),
      derivedPullback t ⋙ derivedPullback s ≅ derivedPullback (s ≫ t) :=
    @Classical.choose _ _ (Classical.choose_spec (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition.{u, w})))
  have hc {A B C : Scheme.{u}} (s : A ⟶ B) (t : B ⟶ C) :
      conjugateEquiv (a (s ≫ t)) ((a t).comp (a s)) (p s t).hom =
        (schemeNormalizedDirectImageCompIso s t).inv := by
    apply (RingedSpace.moduleDirectImage (s ≫ t).toLRSHom.toShHom).rightDerivedFunctor
      |>.rightDerived_ext
        (RingedSpace.moduleDirectImage (s ≫ t).toLRSHom.toShHom).rightDerivedFunctorUnit
        (HomotopyCategory.quasiIso _ (.up ℤ))
    apply NatTrans.ext
    funext K
    exact (derivedPullbackComposition_mate_unit s t K).trans
      ((Classical.choose_spec (RingedSpace.exists_derivedModuleDirectImageComposition
        s.toLRSHom.toShHom t.toLRSHom.toShHom)) K).symm
  have hi {A B C : Scheme.{u}} (s : A ⟶ B) (t : B ⟶ C) :
      conjugateEquiv ((a t).comp (a s)) (a (s ≫ t)) (p s t).inv =
        (schemeNormalizedDirectImageCompIso s t).hom := by
    have he : conjugateIsoEquiv (a (s ≫ t)) ((a t).comp (a s)) (p s t) =
        (schemeNormalizedDirectImageCompIso s t).symm := Iso.ext (hc s t)
    exact congrArg Iso.inv he
  have he {A B : Scheme.{u}} (s t : A ⟶ B) (e : s = t) :
      conjugateEquiv (a s) (a t)
        (eqToHom (congrArg (fun z ↦ derivedPullback z) e.symm)) =
          eqToHom (congrArg (fun z ↦ schemeDerivedDirectImage z) e) := by
    subst t
    simp
  change conjugateEquiv ((a f).comp (a gX)) ((a g).comp (a f'))
    ((p f' g).hom ≫ eqToHom (congrArg (fun t ↦ derivedPullback t) h.symm) ≫
      (p gX f).inv) = _
  rw [← Category.assoc, ← conjugateEquiv_comp _ (a (gX ≫ f))]
  rw [← conjugateEquiv_comp _ (a (f' ≫ g))]
  rw [hi, hc, he _ _ h]

end AlgebraicGeometry
