/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q16
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.CategoryTheory.Comma.Over.Basic

/-! # Relative determinant-one matrix presheaf

Source: Conrad, Reductive group schemes, Proposition 4.3.1, printed p.126
(blueprint: def-sfb-relative-sl2-presheaf).

The values and restriction maps are the existing determinant-one matrix groups and
entrywise ring-map actions. No field, smoothness, or characteristic restriction is used.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry

/-- Entrywise application of the identity ring map fixes determinant-one matrices.
Source: Conrad, Proposition 4.3.1, the functor SL2
(blueprint: def-sfb-relative-sl2-presheaf).
Proof: evaluate both homomorphisms on a matrix and then on each entry; both entries
are the original entry. Subtype and homomorphism extensionality give equality. -/
theorem specialLinear2_map_id (R : CommRingCat.{u}) :
    GrpCat.ofHom (Matrix.SpecialLinearGroup.map (n := Fin 2) (RingHom.id R)) =
      𝟙 (GrpCat.of (Matrix.SpecialLinearGroup (Fin 2) R)) := by
  sorry

/-- Entrywise application respects composition of ring maps.
Source: Conrad, Proposition 4.3.1, the functor SL2
(blueprint: def-sfb-relative-sl2-presheaf).
Proof: on each matrix entry, applying the composite is applying the first ring map
and then the second. Extensionality of matrices, subtypes and group maps concludes. -/
theorem specialLinear2_map_comp {R T V : CommRingCat.{u}} (f : R ⟶ T) (g : T ⟶ V) :
    GrpCat.ofHom (Matrix.SpecialLinearGroup.map (n := Fin 2) (f ≫ g).hom) =
      GrpCat.ofHom (Matrix.SpecialLinearGroup.map (n := Fin 2) f.hom) ≫
        GrpCat.ofHom (Matrix.SpecialLinearGroup.map (n := Fin 2) g.hom) := by
  sorry

/-- The determinant-one 2 by 2 matrix functor on all commutative rings.
Source: Conrad, Proposition 4.3.1 (blueprint: def-sfb-relative-sl2-presheaf). -/
def specialLinear2Functor : CommRingCat.{u} ⥤ GrpCat.{u} where
  obj R := GrpCat.of (Matrix.SpecialLinearGroup (Fin 2) R)
  map f := GrpCat.ofHom (Matrix.SpecialLinearGroup.map f.hom)
  map_id R := specialLinear2_map_id R
  map_comp f g := specialLinear2_map_comp f g

/-- The relative SL2 group presheaf: on T over S it is SL2 of the global sections of T,
and restriction applies the pullback on global sections entrywise.
Source: Conrad, Proposition 4.3.1 (blueprint: def-sfb-relative-sl2-presheaf). -/
def relativeSL2Presheaf (S : Scheme.{u}) : (Over S)ᵒᵖ ⥤ GrpCat.{u} :=
  (Over.forget S).op ⋙ Scheme.Γ ⋙ specialLinear2Functor

end AlgebraicGeometry
