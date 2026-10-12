/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R1
-/
module

public import Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Sheaf.AlgebraicGeometry.RingedSpaceDerivedDirectImageComposition
import Sheaf.AlgebraicGeometry.DerivedDirectImagePreservesQCoh
import Sheaf.AlgebraicGeometry.DerivedDirectImageCompositionUnitLaws
import Sheaf.AlgebraicGeometry.DerivedDirectImageCompositionAssociativity

/-!
# Coherent composition of proper derived direct images

Source: Stacks Project, Cohomology, Tag 0D5T, and Duality for Schemes, Tag 0ATX
(blueprint: lem-pc-proper-derived-direct-image-composition).
-/

@[expose] public section

universe u w

open CategoryTheory

set_option autoImplicit false

namespace AlgebraicGeometry

set_option maxHeartbeats 800000 in
-- Elaborating the comparison witnesses and their dependent coherence clauses.
/-- Proper derived direct images on Noetherian schemes preserve quasi-coherent cohomology
and have canonical, unital and associative composition comparisons. The comparisons are
written after the fully faithful inclusions into the ambient derived categories; together
with preservation this is exactly a comparison on the full quasi-coherent subcategories.
The equation with right-derived units specifies the canonical comparison. Identity and
associativity are component equations, so the reassociations of functor composition are
implicit. The family of derived-category instances chooses only the localizations.
Source: Stacks Project, Cohomology, Tag 0D5T; Duality for Schemes, Tag 0ATX
(blueprint: lem-pc-proper-derived-direct-image-composition).

Proof, step 1: lem-pc-ringed-spaces-derived-adjoint gives Lf* adjoint to Rf* and Lg*
adjoint to Rg*. By lem-pc-ringed-spaces-derived-pullback-composition (Tag 0D5S),
Lg* followed by Lf* identifies with L(gf)*. Transport the composite adjunction;
lem-cat-right-adjoint-composition gives the unique right-adjoint comparison and its
compatibility with the derived units (Tag 0D5T). By
lem-pc-noetherian-derived-direct-image-right-adjoint all these direct images preserve
quasi-coherent cohomology, so the comparison restricts to the full subcategories.
Step 2: the identity and associativity laws for derived pullbacks from
lem-pc-ringed-spaces-derived-pullback-composition pass to their conjugate comparisons
by lem-cat-right-adjoint-composition. Mates preserve identities and composition, giving
both unit equations and the triple-composition equation below. -/
theorem exists_properDerivedDirectImageComposition
    [d : ∀ X : Scheme.{u}, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings X.toRingedSpace))] :
    ∃ p : ∀ {X Y : Scheme.{u}} [IsNoetherian X]
        [IsNoetherian Y] (f : X ⟶ Y) [IsProper f],
        ∀ E : schemeDerivedQCohCategory X,
          schemeDerivedQCohProperty Y ((schemeDerivedDirectImage f).obj E.obj),
    ∃ c : ∀ {X Y Z : Scheme.{u}} [IsNoetherian X]
        [IsNoetherian Y] [IsNoetherian Z]
        (f : X ⟶ Y) (g : Y ⟶ Z) [IsProper f] [IsProper g],
        (schemeDerivedQCohProperty X).ι ⋙
            (schemeDerivedDirectImage f ⋙ schemeDerivedDirectImage g) ≅
          (schemeDerivedQCohProperty X).ι ⋙ schemeDerivedDirectImage (f ≫ g),
      (∀ {X Y Z : Scheme.{u}} [IsNoetherian X]
        [IsNoetherian Y] [IsNoetherian Z]
        (f : X ⟶ Y) (g : Y ⟶ Z) [IsProper f] [IsProper g]
        (K : HomotopyCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace))
          (ComplexShape.up ℤ)) (hK : schemeDerivedQCohProperty X (DerivedCategory.Qh.obj K)),
        (RingedSpace.moduleDirectImage (f ≫ g).toLRSHom.toShHom).rightDerivedFunctorUnit.app K ≫
            (c f g).inv.app ⟨DerivedCategory.Qh.obj K, hK⟩ =
          (RingedSpace.moduleDirectImage g.toLRSHom.toShHom).rightDerivedFunctorUnit.app
              (((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).mapHomotopyCategory
                (ComplexShape.up ℤ)).obj K) ≫
            (schemeDerivedDirectImage g).map
              ((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).rightDerivedFunctorUnit.app
                K)) ∧
      ∃ i : ∀ (X : Scheme.{u}) [IsNoetherian X],
          (schemeDerivedQCohProperty X).ι ⋙ schemeDerivedDirectImage (𝟙 X) ≅
            (schemeDerivedQCohProperty X).ι,
        (∀ {X Y : Scheme.{u}} [IsNoetherian X]
          [IsNoetherian Y] (f : X ⟶ Y) [IsProper f]
          (E : schemeDerivedQCohCategory X),
          (c (𝟙 X) f).hom.app E ≫
              eqToHom (congrArg (fun k : X ⟶ Y => (schemeDerivedDirectImage k).obj E.obj)
                (Category.id_comp f)) =
            (schemeDerivedDirectImage f).map ((i X).hom.app E)) ∧
        (∀ {X Y : Scheme.{u}} [IsNoetherian X]
          [IsNoetherian Y] (f : X ⟶ Y) [IsProper f]
          (E : schemeDerivedQCohCategory X),
          (c f (𝟙 Y)).hom.app E ≫
              eqToHom (congrArg (fun k : X ⟶ Y => (schemeDerivedDirectImage k).obj E.obj)
                (Category.comp_id f)) =
            (i Y).hom.app ⟨(schemeDerivedDirectImage f).obj E.obj, p f E⟩) ∧
        (∀ {W X Y Z : Scheme.{u}} [IsNoetherian W]
          [IsNoetherian X] [IsNoetherian Y]
          [IsNoetherian Z]
          (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) [IsProper f] [IsProper g] [IsProper h]
          (E : schemeDerivedQCohCategory W),
          (schemeDerivedDirectImage h).map ((c f g).hom.app E) ≫
              (c (f ≫ g) h).hom.app E ≫
              eqToHom (congrArg (fun k : W ⟶ Z => (schemeDerivedDirectImage k).obj E.obj)
                (Category.assoc f g h)) =
            (c g h).hom.app ⟨(schemeDerivedDirectImage f).obj E.obj, p f E⟩ ≫
              (c f (g ≫ h)).hom.app E) := by
  classical
  let p : ∀ {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y] (f : X ⟶ Y)
      [IsProper f], ∀ E : schemeDerivedQCohCategory X,
      schemeDerivedQCohProperty Y ((schemeDerivedDirectImage f).obj E.obj) := by
    intro X Y hX hY f hf E
    exact schemeDerivedDirectImage_preserves_QCoh f E.obj E.property
  let c₀ : ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z),
      schemeDerivedDirectImage f ⋙ schemeDerivedDirectImage g ≅
        schemeDerivedDirectImage (f ≫ g) := fun f g ↦
    (RingedSpace.exists_derivedModuleDirectImageComposition
      f.toLRSHom.toShHom g.toLRSHom.toShHom).choose
  have hc₀ : ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
      (K : HomotopyCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace))
        (ComplexShape.up ℤ)),
      (RingedSpace.moduleDirectImage (f ≫ g).toLRSHom.toShHom).rightDerivedFunctorUnit.app K ≫
          (c₀ f g).inv.app (DerivedCategory.Qh.obj K) =
        (RingedSpace.moduleDirectImage g.toLRSHom.toShHom).rightDerivedFunctorUnit.app
            (((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).mapHomotopyCategory
              (ComplexShape.up ℤ)).obj K) ≫
          (schemeDerivedDirectImage g).map
            ((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).rightDerivedFunctorUnit.app K) := by
    intro X Y Z f g K
    exact (RingedSpace.exists_derivedModuleDirectImageComposition
      f.toLRSHom.toShHom g.toLRSHom.toShHom).choose_spec K
  let c : ∀ {X Y Z : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
      [IsNoetherian Z] (f : X ⟶ Y) (g : Y ⟶ Z) [IsProper f] [IsProper g],
      (schemeDerivedQCohProperty X).ι ⋙
          (schemeDerivedDirectImage f ⋙ schemeDerivedDirectImage g) ≅
        (schemeDerivedQCohProperty X).ι ⋙ schemeDerivedDirectImage (f ≫ g) := by
    intro X Y Z hX hY hZ f g hf hg
    exact Functor.isoWhiskerLeft (schemeDerivedQCohProperty X).ι (c₀ f g)
  obtain ⟨i₀, hi₁, hi₂⟩ := derivedDirectImageComposition_unit_laws c₀ hc₀
  let i : ∀ (X : Scheme.{u}) [IsNoetherian X],
      (schemeDerivedQCohProperty X).ι ⋙ schemeDerivedDirectImage (𝟙 X) ≅
        (schemeDerivedQCohProperty X).ι := fun X ↦
    Functor.isoWhiskerLeft (schemeDerivedQCohProperty X).ι (i₀ X) ≪≫
      Functor.rightUnitor (schemeDerivedQCohProperty X).ι
  refine ⟨p, c, ?_, i, ?_, ?_, ?_⟩
  · intro X Y Z hX hY hZ f g hf hg K hK
    exact hc₀ f g K
  · intro X Y hX hY f hf E
    simpa [c, i] using hi₁ f E.obj
  · intro X Y hX hY f hf E
    simpa [c, i] using hi₂ f E.obj
  · intro W X Y Z hW hX hY hZ f g h hf hg hh E
    exact derivedDirectImageComposition_associativity c₀ hc₀ f g h E.obj

end AlgebraicGeometry
