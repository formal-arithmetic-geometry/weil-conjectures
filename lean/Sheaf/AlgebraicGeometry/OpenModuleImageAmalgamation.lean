/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B3
-/
module

public import Sheaf.AlgebraicGeometry.KInjectiveMayerVietorisData

/-! # OpenModuleImageAmalgamation

Source: Stacks Project, Cohomology, Tags 08BV and 01EB.
(blueprint: lem-pc-open-module-image-gluing-existence).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits TopologicalSpace
set_option autoImplicit false
namespace AlgebraicGeometry

/-- Existence half of the sheaf gluing universal property.
Source: Stacks Project, Cohomology, Tags 08BV and 01EB.
(blueprint: lem-pc-open-module-image-gluing-existence)
Proof: At each test open T and each section z of Z(T), identify the two image
objects' sections with M(T ∩ U) and M(T ∩ V) via overFunctorEquiv. The ordinary
restriction unit is the restriction map by restrictAdjunction_unit_app_app.
In the overlap mate the inverse composition comparison, restricted counit, and
forward comparison cancel repeated restriction and give restriction to T ∩ U ∩ V.
The compatibility hypothesis therefore says b(z) and c(z) agree there. Since
(T ∩ U) ∪ (T ∩ V) = T, the sheaf axiom gives an amalgamation in M(T).
Uniqueness of section amalgamation proves compatibility with restriction in T:
both restrictions have the same images on the two covering opens. It also proves
additivity and linearity, since the sum or scalar multiple of amalgamations has
the prescribed restrictions. These sectionwise linear maps assemble to a module
sheaf morphism l, and the two gluing equations give the required composites.
The empty scheme, empty covering member, and repeated opens use the same axiom.
-/
theorem schemeOpenModuleImage_pullback_exists
    (X : Scheme.{u}) (U V : X.Opens) (hcover : U ⊔ V = ⊤)
    (M : SheafOfModules.{u} (moduleRings X.toRingedSpace))
    {Z : SheafOfModules.{u} (moduleRings X.toRingedSpace)}
    (b : Z ⟶ (schemeOpenModuleImage X U).obj M)
    (c : Z ⟶ (schemeOpenModuleImage X V).obj M)
    (hbc : b ≫ (schemeOpenModuleImageRestriction X
      (homOfLE (inf_le_left : U ⊓ V ≤ U))).app M =
      c ≫ (schemeOpenModuleImageRestriction X
        (homOfLE (inf_le_right : U ⊓ V ≤ V))).app M) :
    ∃ l : Z ⟶ M,
      l ≫ (schemeOpenModuleAdjunction X U).unit.app M = b ∧
      l ≫ (schemeOpenModuleAdjunction X V).unit.app M = c := by
  sorry

end AlgebraicGeometry
