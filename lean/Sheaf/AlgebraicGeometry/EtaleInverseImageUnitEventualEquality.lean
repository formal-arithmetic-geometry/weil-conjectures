/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S1
-/
module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance

/-! # Eventual equality for a single inverse-image unit

Source: Stacks Project, Sites Tag 0A35 and Etale Cohomology Tag 09YQ.
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale

/-- Equality under the inverse-image unit for one stage sheaf is detected by
an inverse-image unit at a later scheme stage.
Source: Stacks Project, Sites Tag 0A35 (lemma-compute-pullback-to-limit),
and Etale Cohomology Tags 0EYL, 04HR and 09YQ.
(blueprint: lem-weil-pbc-etale-inverse-image-unit-eventual-equality).

Proof: Restrict the system to the cofinal directed tail above i. Cover U by
finitely many affine opens. The affine transition maps preserve affineness after
base change. Present the limit affine etale site by the filtered colimit of
stage affine etale sites (0EYL). Restriction to this basis is an equivalence of
sheaf categories (04HR). The inverse-image section formula of 0A35, applied to
this single sheaf, identifies the limit unit images with images of the original
sections in the filtered colimit of sections of its stage inverse images.
Equality of these images is witnessed at a later stage. The adjunction unit
formula identifies the witness maps with the displayed units. Do this on each
of the finitely many affine opens, choose a common later stage, and use unit
naturality and separatedness on the pulled-back cover to obtain equality on U.
This does not involve any colimit of varying sheaves. For empty U the sheaf
condition for the empty covering gives equality already at i; a zero sheaf and
a singleton directed index satisfy the same argument. -/
theorem etale_inverse_image_unit_eventual_equality
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ i : Iᵒᵖ, CompactSpace (D.obj i)]
    [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]
    [∀ (i j : Iᵒᵖ) (f : i ⟶ j), IsAffineHom (D.map f)]
    (i : I) (F : Sheaf (D.obj (op i)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (U : (D.obj (op i)).Etale) [CompactSpace U.left] [QuasiSeparatedSpace U.left]
    (s t : F.obj.obj (op U))
    (hst : ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1}
        (c.π.app (op i))).unit.app F).hom.app (op U) s =
      ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1}
        (c.π.app (op i))).unit.app F).hom.app (op U) t) :
    ∃ (k : I) (a : i ⟶ k),
      ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1}
        (D.map a.op)).unit.app F).hom.app (op U) s =
      ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1}
        (D.map a.op)).unit.app F).hom.app (op U) t := by sorry

end AlgebraicGeometry.Etale
