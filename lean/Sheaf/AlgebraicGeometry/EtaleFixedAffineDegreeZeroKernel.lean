/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group X2
-/
module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance

/-! # Finite-stage vanishing for one fixed sheaf in degree zero

Source: Stacks Project, Tags 09YQ, 0EYL, 04HR and 09YN.
(blueprint: lem-weil-pbc-fixed-affine-degree-zero-kernel).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale

/-- A degree-zero class of a single stage sheaf which dies on the affine inverse
limit dies after pullback to a later stage. No varying coefficient system or colimit
of sheaves is involved.

Source: Stacks Project, Tag 09YQ, degree-zero argument via 0EYL, 04HR and 09YN.
(blueprint: lem-weil-pbc-fixed-affine-degree-zero-kernel).

Proof: Restrict the inverse system to the cofinal upper tail of i. Its schemes and
limit are affine. Present the limit affine etale site as the colimit of the stage
sites (0EYL), and restrict the fixed sheaf and all its inverse images along the
small-to-affine equivalences (04HR). Inverse-image composition identifies the
pullbacks on the limit with the constant diagram on the limit inverse image of F;
these identifications commute with the units, so its identity cocone is a colimit.
Apply 09YN at the identity affine object. The resulting filtered colimit of stage
sections is the group of limit sections, with transition maps induced by the units.
The identification H^0 = sections carries cohomologyMap to these unit maps.
The zero image of x is therefore equality of its representative with zero in a
filtered colimit. The equality criterion supplies a stage on the upper tail where
the pulled-back representative is zero. The tail inclusion gives the displayed
arrow in I. For zero coefficients or an empty affine scheme, every section is zero;
for a singleton index, pullback along the limit projection is an equivalence.
-/
theorem fixed_affine_degree_zero_kernel
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ i : Iᵒᵖ, IsAffine (D.obj i)]
    [∀ (i j : Iᵒᵖ) (f : i ⟶ j), IsAffineHom (D.map f)]
    (i : I) (F : Sheaf (D.obj (op i)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (x : Sheaf.H F 0) (hx : cohomologyMap (c.π.app (op i)) F 0 x = 0) :
    ∃ (j : I) (f : i ⟶ j), cohomologyMap (D.map f.op) F 0 x = 0 := by sorry

end AlgebraicGeometry.Etale
