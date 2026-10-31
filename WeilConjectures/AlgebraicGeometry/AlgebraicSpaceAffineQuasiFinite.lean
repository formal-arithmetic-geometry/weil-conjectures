/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! # Affine and quasi-finite morphisms of algebraic spaces

Source: Stacks Project, Morphisms of Spaces, definitions affine and quasi-finite;
Spaces Descent, Tags 041Z and 0427
(blueprint: def-sfb-space-affine-quasifinite-properties).

Quasi-finiteness uses the literal finite-geometric-fibre convention of the consumer.
Finite type and field-valued point classes are the existing library notions.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- An affine scheme test of an affine map is represented by an affine scheme.
The pullback square fixes both its projection and its map to the source.
Source: Stacks, Morphisms of Spaces, definition-affine; Spaces Descent, Tag 041Z
(blueprint: def-sfb-space-affine-quasifinite-properties). -/
def MapIsAffine {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) : Prop :=
  ∀ (T : Over S) (_ : IsAffine T.left) (a : yoneda.obj T ⟶ Y.obj.obj),
    ∃ (U : Over S) (_ : IsAffine U.left) (p : U ⟶ T) (q : yoneda.obj U ⟶ X.obj.obj),
      IsPullback q (yoneda.map p) f.hom.hom a

/-- Finite type with finite sets of points in every algebraically closed field fibre.
`Point` is the existing quotient of field-valued representatives by common extension.
Source: Stacks, Morphisms of Spaces, definition-quasi-finite; Spaces Descent, Tag 0427,
and the finite-geometric-fibre convention of lem-sfb-space-four-property-fppf-descent
(blueprint: def-sfb-space-affine-quasifinite-properties). -/
def MapIsQuasiFinite {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) : Prop :=
  MapIsFiniteType f ∧
    ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (CommRingCat.of Ω) ⟶ S)
      (a : yoneda.obj (Over.mk s) ⟶ Y.obj.obj),
      Finite (Point (Limits.pullback f.hom.hom a))

end AlgebraicGeometry.AlgebraicSpace
