/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AlgebraicSpace

/-!
# Joint surjectivity on points of algebraic spaces

Source: Stacks Project, Properties of Spaces, Tag 03BU; Topologies on Algebraic Spaces,
Tag 041F (blueprint: def-trf-algebraic-space-jointly-surjective-family).

The quotient-point condition is expanded on field-valued representatives: after extending
the representative's field, it lifts to one member of the family. A representative in a
source over a different field can be restricted to the common extension appearing in the
point equivalence relation. Thus no quotient or choice of point representatives is needed.
-/

@[expose] public section

universe u w

open CategoryTheory Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- A family is jointly surjective on points if every field-valued representative lifts
through a family member after a field extension. This is the union-of-images condition on
point classes of Tag 03BU: restrict a source representative to a common extension; in the
reverse direction, the displayed extension itself witnesses equality of the point classes.
All spectra and extension fields belong to the universe of the big site.
Source: Stacks, Properties of Spaces, Tag 03BU, and Topologies on Algebraic Spaces, Tag 041F
(blueprint: def-trf-algebraic-space-jointly-surjective-family). -/
def IsJointlySurjective {S : Scheme.{u}} {I : Type w}
    {F : (Over S)ᵒᵖ ⥤ Type u} {G : I → (Over S)ᵒᵖ ⥤ Type u}
    (f : ∀ i : I, G i ⟶ F) : Prop :=
  ∀ (K : Type u) [Field K] (s : Spec (CommRingCat.of K) ⟶ S)
    (x : F.obj (op (Over.mk s))),
    ∃ (i : I) (L : Type u) (_ : Field L) (e : K →+* L)
      (y : (G i).obj (op (Over.mk (Spec.map (CommRingCat.ofHom e) ≫ s)))),
      (f i).app _ y =
        F.map (Over.homMk (Spec.map (CommRingCat.ofHom e)) rfl).op x

end AlgebraicGeometry.AlgebraicSpace
