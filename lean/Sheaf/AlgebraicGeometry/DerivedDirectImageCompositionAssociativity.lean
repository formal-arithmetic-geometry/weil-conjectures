/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A3
-/
module

public import Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage
import Sheaf.AlgebraicGeometry.DerivedCategory

/-!
# Coherence of canonical unbounded derived direct images

Source: Stacks Project, Cohomology, Tag 0D5T and its derived universal property.
-/

@[expose] public section

universe u w

open CategoryTheory

set_option autoImplicit false

namespace AlgebraicGeometry

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
  sorry

end AlgebraicGeometry
