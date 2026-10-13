/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J2
-/
module

public import Sheaf.AlgebraicGeometry.DerivedTensorStructure
public import Sheaf.AlgebraicGeometry.DerivedPullback
public import Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage

/-! # Functor comparisons across a scheme-isomorphism square

Source: Stacks Project, Tag 08EU, affine-local reduction, expanded by the
K-flat and K-injective constructions of Tags 06YI and 079V.
(blueprint: lem-pc-scheme-iso-derived-functor-comparisons).
-/

@[expose] public section

universe u w w'
open CategoryTheory MonoidalCategory
namespace AlgebraicGeometry
set_option autoImplicit false

/-- Tensor, pullback and direct-image comparisons for equivalences induced by
scheme isomorphisms. No adjunction or projection mate is part of this assertion.

Source: Stacks Project, Tag 08EU, first sentence of the proof, expanded using
Tags 06YI and 079V; step 1 of lem-pc-projection-mate-scheme-iso-transport.
(blueprint: lem-pc-scheme-iso-derived-functor-comparisons).

Proof: Pushforward along each scheme isomorphism and its inverse are exact
inverse equivalences of module categories. The supplied localization comparisons
identify a and b with their termwise pushforwards on complexes. Underived
isomorphism pushforward commutes with tensor: on every stalk the ring map is an
isomorphism and the tensor comparison is extension/restriction of scalars along
that ring isomorphism. Exact inverse equivalences preserve K-flat complexes:
tensoring an acyclic complex can be tested after the inverse exact equivalence.
Compute tensor on K-flat resolutions, apply the underived tensor comparisons,
and descend these comparisons and their inverses through localization in each
variable. This gives the first two natural isomorphisms.

For pullback, the commuting scheme square identifies the underived composites
(eY)_* followed by f* and g* followed by (eX)_*. On a K-flat resolution both
left derived functors are represented by this composite, since isomorphism
pushforward preserves K-flatness. The uniqueness of the left derived functor
extends the representative comparison to the third natural isomorphism.
For direct image use K-injective resolutions. An exact equivalence preserves
K-injectivity by transporting the Hom complex from an acyclic complex through
its exact inverse. Composition of underived direct images and the commuting
square identify the complexes obtained by g_* then (eY)_* and by (eX)_* then f_*.
Their localizations give the fourth natural isomorphism, independent of the
resolution by the right derived universal property. The localization universal
properties apply also when w and w' differ. Empty schemes and zero complexes
require no separate choice or nonemptiness hypothesis. -/
theorem schemeIso_derived_functor_comparisons
    (X Y X' Y' : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [HasDerivedCategory.{w'} (SheafOfModules.{u} (moduleRings X'.toRingedSpace))]
    [HasDerivedCategory.{w'} (SheafOfModules.{u} (moduleRings Y'.toRingedSpace))]
    (f : X ⟶ Y) (g : X' ⟶ Y') (eX : X' ≅ X) (eY : Y' ≅ Y)
    (hcomm : g ≫ eY.hom = eX.hom ≫ f)
    (a : schemeDerivedCategory Y' ≌ schemeDerivedCategory Y)
    (b : schemeDerivedCategory X' ≌ schemeDerivedCategory X)
    (ha : DerivedCategory.Q ⋙ a.functor ≅
      (@Functor.mapHomologicalComplex ℤ
        (SheafOfModules.{u} (moduleRings Y'.toRingedSpace))
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) _ _ _ _
        (SheafOfModules.pushforward eY.hom.toRingCatSheafHom)
        ⟨fun _ _ ↦ rfl⟩ (ComplexShape.up ℤ)) ⋙ DerivedCategory.Q)
    (hb : DerivedCategory.Q ⋙ b.functor ≅
      (@Functor.mapHomologicalComplex ℤ
        (SheafOfModules.{u} (moduleRings X'.toRingedSpace))
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) _ _ _ _
        (SheafOfModules.pushforward eX.hom.toRingCatSheafHom)
        ⟨fun _ _ ↦ rfl⟩ (ComplexShape.up ℤ)) ⋙ DerivedCategory.Q) :
    Nonempty (tensor (schemeDerivedCategory Y') ⋙ a.functor ≅
      a.functor.prod a.functor ⋙ tensor (schemeDerivedCategory Y)) ∧
    Nonempty (tensor (schemeDerivedCategory X') ⋙ b.functor ≅
      b.functor.prod b.functor ⋙ tensor (schemeDerivedCategory X)) ∧
    Nonempty (a.functor ⋙ derivedPullback f ≅ derivedPullback g ⋙ b.functor) ∧
    Nonempty (schemeDerivedDirectImage g ⋙ a.functor ≅
      b.functor ⋙ schemeDerivedDirectImage f) := by sorry

end AlgebraicGeometry
