/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A3
-/
module

public import Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage

/-!
# Coherence of canonical unbounded derived direct images

Source: Stacks Project, Cohomology, Tag 0D5T and its derived universal property.
-/

@[expose] public section

universe u w

open CategoryTheory

set_option autoImplicit false

namespace AlgebraicGeometry

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
  sorry

end AlgebraicGeometry
