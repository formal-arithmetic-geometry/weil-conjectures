/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V2
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.Algebra.Category.Ring.Colimits

/-!
# Coordinate rings of an affine open over a directed inverse system

Source: Stacks Project, Limits, Tags 01YX and 01YW.
(blueprint: lem-weil-pbc-affine-open-directed-ring-system).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- An affine open and its inverse images have compatible spectrum presentations over
an upper-tail coordinate-ring diagram, including its colimit.

Source: Stacks Project, Limits, Tags 01YX and 01YW.
(blueprint: lem-weil-pbc-affine-open-directed-ring-system).

Proof: Restrict D to the upper tail J, and at i take the inverse image W_i of W.
For i ≤ j the restricted transition W_j → W_i induces a ring map on global
sections; these maps define the covariant functor F. Affine transition morphisms
make every W_i affine. At the least index o, D.map(id) = id identifies W_o
with W, giving e0 : W ≅ Spec(F(o)). The affine spectrum presentations e_i
are natural for the restricted transitions; hence their squares with the maps
to W give the asserted compatibility with F(o → i). The upper tail opposite
is equivalent to Over(op i₀). Under this equivalence the restricted cone is
opensCone D c (op i₀) W, limiting by isLimitOpensCone. Applying Spec to the
opposite of the colimit cocone of F gives another limiting cone, because Spec
is a right adjoint. The unique comparison of limiting cones gives eL. Its
commutation with the leg at o gives exactly the last equality, so the algebra
structure at the limit is the coprojection, rather than an arbitrary ring map.
This argument also covers the empty affine open: its coordinate ring and all
rings of the diagram are the zero ring. -/
theorem exists_affineOpen_directedRingSystem
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]
    (c : Cone D) (hc : IsLimit c) (i₀ : I)
    (W : (D.obj (op i₀)).Opens) (hW : IsAffineOpen W) :
    ∃ (F : {i : I // i₀ ≤ i} ⥤ CommRingCat.{u})
      (e0 : W.toScheme ≅ Spec (F.obj ⟨i₀, le_rfl⟩)),
      (∀ i : {i : I // i₀ ≤ i},
        ∃ e : (D.map (homOfLE i.property).op ⁻¹ᵁ W).toScheme ≅ Spec (F.obj i),
          (D.map (homOfLE i.property).op).resLE W _ le_rfl ≫ e0.hom =
            e.hom ≫ Spec.map (F.map (homOfLE i.property))) ∧
      ∃ eL : (c.π.app (op i₀) ⁻¹ᵁ W).toScheme ≅ Spec (colimit F),
        (c.π.app (op i₀)).resLE W _ le_rfl ≫ e0.hom =
          eL.hom ≫ Spec.map (colimit.ι F ⟨i₀, le_rfl⟩) := by sorry

end AlgebraicGeometry
