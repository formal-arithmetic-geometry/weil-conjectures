/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q7
-/
module

public import Sheaf.Topology.SpectralLimitCohomologyMap
public import Mathlib.CategoryTheory.Adjunction.Additive

/-! # Normalized cohomology respects composition of two f-maps

Source: Stacks Project, Cohomology of Sheaves, Tags 01F7, 01F8 and 0A37.
(blueprint: lem-weil-pbc-spectral-limit-fmap-composition)
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open CategoryTheory.Functor.sheafPullbackConstruction
namespace TopCat.Sheaf

/-- Normalized cohomology respects composition of two f-maps.
Source: Stacks Project, Cohomology of Sheaves, Tags 01F7, 01F8 and 0A37.
(blueprint: lem-weil-pbc-spectral-limit-fmap-composition)

Proof: Compare the pure pullback along the composite with the successive pullbacks
using the unit-compatible left-adjoint uniqueness isomorphism. In degree zero,
evaluation on the universal free-sheaf generator and the adjunction unit equation
identify the maps. In positive degrees embed the source coefficient sheaf into
an injective and form its cokernel sequence. Positive Ext into the injective
vanishes, so its Yoneda boundary is surjective. Exact inverse image preserves the
sequence. The given boundary compatibilities, naturality of extension classes
under the comparison isomorphism, and induction identify the two pullbacks.
Finally transpose α and β through the adjunctions: the transpose of their
composite is the comparison isomorphism followed by the pullback of the
transpose of α and then the transpose of β. Naturality in coefficients and
functoriality of cohomology give the displayed equation. -/
theorem spectralLimitCohomologyMap_comp {X Y Z : TopCat.{u}}
    (f : X ⟶ Y) (g : Z ⟶ X) (h : Z ⟶ Y) (he : g ≫ f = h)
    (cf : SiteCohomologyFamily (Opens.grothendieckTopology Y)
      (Opens.grothendieckTopology X) (Opens.map f))
    (cg : SiteCohomologyFamily (Opens.grothendieckTopology X)
      (Opens.grothendieckTopology Z) (Opens.map g))
    (ch : SiteCohomologyFamily (Opens.grothendieckTopology Y)
      (Opens.grothendieckTopology Z) (Opens.map h))
    (hf : @SiteCohomologyFamily.IsPullback _ _ _ _
      (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)
      (Opens.map f) inferInstance
      (@Adjunction.left_adjoint_additive _ _ _ _ _ _ _ _
        (sheafAdjunctionContinuous (Opens.map f) AddCommGrpCat.{u}
          (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X))
        (Functor.additive_of_preserves_binary_products _))
      inferInstance inferInstance cf)
    (hg : @SiteCohomologyFamily.IsPullback _ _ _ _
      (Opens.grothendieckTopology X) (Opens.grothendieckTopology Z)
      (Opens.map g) inferInstance
      (@Adjunction.left_adjoint_additive _ _ _ _ _ _ _ _
        (sheafAdjunctionContinuous (Opens.map g) AddCommGrpCat.{u}
          (Opens.grothendieckTopology X) (Opens.grothendieckTopology Z))
        (Functor.additive_of_preserves_binary_products _))
      inferInstance inferInstance cg)
    (hh : @SiteCohomologyFamily.IsPullback _ _ _ _
      (Opens.grothendieckTopology Y) (Opens.grothendieckTopology Z)
      (Opens.map h) inferInstance
      (@Adjunction.left_adjoint_additive _ _ _ _ _ _ _ _
        (sheafAdjunctionContinuous (Opens.map h) AddCommGrpCat.{u}
          (Opens.grothendieckTopology Y) (Opens.grothendieckTopology Z))
        (Functor.additive_of_preserves_binary_products _))
      inferInstance inferInstance ch)
    {A : CategoryTheory.Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}}
    {B : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}
    {C : CategoryTheory.Sheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{u}}
    (α : A ⟶ (pushforward AddCommGrpCat.{u} f).obj B)
    (β : B ⟶ (pushforward AddCommGrpCat.{u} g).obj C)
    (γ : A ⟶ (pushforward AddCommGrpCat.{u} h).obj C)
    (hγ : ∀ (U : Opens Y) (s : A.obj.obj (op U)),
      HEq ((γ.hom.app (op U)).hom s)
        ((β.hom.app (op ((Opens.map f).obj U))).hom ((α.hom.app (op U)).hom s)))
    (q : ℕ) :
    spectralLimitCohomologyMap f cf α q ≫ spectralLimitCohomologyMap g cg β q =
      spectralLimitCohomologyMap h ch γ q := by sorry

end TopCat.Sheaf
