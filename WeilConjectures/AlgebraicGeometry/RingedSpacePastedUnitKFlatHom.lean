/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.Localization
public import WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedDirectImage
public import WeilConjectures.Algebra.Homology.KFlat
import all Mathlib.Algebra.Homology.Localization
import WeilConjectures.AlgebraicGeometry.RingedSpacePastedPullbackAdjunction
import WeilConjectures.AlgebraicGeometry.RingedSpaceKFlatDirectImageHomLocalization

/-!
# The pasted direct-image unit tested on K-flat complexes

## References

* [Stacks Project, Tag 079W](https://stacks.math.columbia.edu/tag/079W)
* [Stacks Project, Tag 0D5S](https://stacks.math.columbia.edu/tag/0D5S)
* [Stacks Project, Tag 0D5T](https://stacks.math.columbia.edu/tag/0D5T)
-/

@[expose] public section

universe u wX wY wZ

open CategoryTheory

set_option autoImplicit false

namespace AlgebraicGeometry.RingedSpace

private theorem hom_bijective_of_compatible_adjunctions
    {C D DC DD : Type*} [Category* C] [Category* D] [Category* DC] [Category* DD]
    {G : C ⥤ D} {F : D ⥤ C} (adj : G ⊣ F)
    {G' : DC ⥤ DD} {F' : DD ⥤ DC} (adj' : G' ⊣ F')
    (Q₁ : C ⥤ DC) (Q₂ : D ⥤ DD)
    (α : Q₁ ⋙ G' ⟶ G ⋙ Q₂) (β : F ⋙ Q₁ ⟶ Q₂ ⋙ F')
    (hη : ∀ X, adj'.unit.app (Q₁.obj X) ≫ F'.map (α.app X) =
      Q₁.map (adj.unit.app X) ≫ β.app (G.obj X))
    (K : C) (I : D) [IsIso (α.app K)]
    (hQ : Function.Bijective (Q₂.map : (G.obj K ⟶ I) → _)) :
    Function.Bijective (fun a : K ⟶ F.obj I ↦ Q₁.map a ≫ β.app I) := by
  let e := Iso.homCongr (asIso (α.app K)).symm (Iso.refl (Q₂.obj I))
  have hb := (adj'.homEquiv (Q₁.obj K) (Q₂.obj I)).bijective.comp
    (e.bijective.comp (hQ.comp (adj.homEquiv K I).symm.bijective))
  convert! hb using 1
  funext a
  dsimp [Function.comp, e, Iso.homCongr]
  rw [Category.comp_id, Adjunction.homEquiv_unit, Functor.map_comp,
    ← Category.assoc, hη, Category.assoc]
  have hn := β.naturality ((adj.homEquiv K I).symm a)
  dsimp at hn
  rw [← hn]
  rw [← Category.assoc, ← Q₁.map_comp]
  have ha := (adj.homEquiv K I).apply_symm_apply a
  rw [Adjunction.homEquiv_unit] at ha
  rw [ha]

/-- Postcomposition with the pasted derived units induces a Hom bijection when the
source is a localized K-flat complex and the original target is K-injective. -/
theorem moduleDirectImage_pastedUnit_kFlat_hom_bijective
    {X Y Z : RingedSpace.{u}}
    [HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X))]
    [HasDerivedCategory.{wY} (SheafOfModules.{u} (moduleRings Y))]
    [HasDerivedCategory.{wZ} (SheafOfModules.{u} (moduleRings Z))]
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (I : CochainComplex (SheafOfModules.{u} (moduleRings X)) ℤ) [I.IsKInjective]
    (K : CochainComplex (SheafOfModules.{u} (moduleRings Z)) ℤ) (hK : K.IsKFlatTensor) :
    Function.Bijective (fun
      (a : DerivedCategory.Q.obj K ⟶ DerivedCategory.Qh.obj
        (((moduleDirectImage g).mapHomotopyCategory (ComplexShape.up ℤ)).obj
          (((moduleDirectImage f).mapHomotopyCategory (ComplexShape.up ℤ)).obj
            ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I)))) =>
      a ≫ (moduleDirectImage g).rightDerivedFunctorUnit.app
          (((moduleDirectImage f).mapHomotopyCategory (ComplexShape.up ℤ)).obj
            ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I)) ≫
        (derivedModuleDirectImage g).map
          ((moduleDirectImage f).rightDerivedFunctorUnit.app
            ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I))) := by
  obtain ⟨G, adj, L, adj', α, hα, hη⟩ := exists_pasted_tensorPullback_adjunction f g
  let K₀ := (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K
  let I₀ := (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I
  let β := (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft
      ((moduleDirectImage f).mapHomotopyCategory (ComplexShape.up ℤ))
      (moduleDirectImage g).rightDerivedFunctorUnit ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (moduleDirectImage f).rightDerivedFunctorUnit
      (derivedModuleDirectImage g) ≫ (Functor.associator _ _ _).hom
  let : IsIso (α.app K₀) := hα K hK
  have hb := hom_bijective_of_compatible_adjunctions adj adj'
    DerivedCategory.Qh DerivedCategory.Qh α β hη K₀ I₀
    (CochainComplex.IsKInjective.Qh_map_bijective (G.obj K₀) I)
  have hloc := moduleDirectImage_kFlat_hom_localization_bijective f g I K hK
  have hβ : β.app I₀ =
      (moduleDirectImage g).rightDerivedFunctorUnit.app
        (((moduleDirectImage f).mapHomotopyCategory (ComplexShape.up ℤ)).obj I₀) ≫
      (derivedModuleDirectImage g).map
        ((moduleDirectImage f).rightDerivedFunctorUnit.app I₀) := by
    simp [β]
  constructor
  · intro a b hab
    obtain ⟨a₀, rfl⟩ := hloc.surjective a
    obtain ⟨b₀, rfl⟩ := hloc.surjective b
    congr 1
    apply hb.injective
    simpa only [hβ, Category.assoc] using hab
  · intro b
    obtain ⟨a, ha⟩ := hb.surjective b
    refine ⟨DerivedCategory.Qh.map a, ?_⟩
    simpa only [hβ, Category.assoc] using ha

end AlgebraicGeometry.RingedSpace
