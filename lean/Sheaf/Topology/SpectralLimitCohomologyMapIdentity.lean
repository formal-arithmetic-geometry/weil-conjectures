/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q7
-/
module

public import Sheaf.Topology.SpectralLimitCohomologyMap
public import Mathlib.CategoryTheory.Adjunction.Additive

/-! # Normalized cohomology of an identity f-map

Source: Stacks Project, Cohomology of Sheaves, Tags 01F7, 01F8 and 0A37.
(blueprint: lem-weil-pbc-spectral-limit-fmap-identity)
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open CategoryTheory.Functor.sheafPullbackConstruction
namespace TopCat.Sheaf

/-- Normalized cohomology of an identity f-map.
Source: Stacks Project, Cohomology of Sheaves, Tags 01F7, 01F8 and 0A37.
(blueprint: lem-weil-pbc-spectral-limit-fmap-identity)

Proof: Sectionwise extensionality identifies α with the identity coefficient
arrow. Compare the normalized pullback along the identity with the identity
family using the unit-compatible isomorphism from its inverse image to the
identity functor. The degree-zero generator evaluation and adjunction unit law
identify these maps. Embed each coefficient sheaf into an injective and take
the cokernel. Positive Ext into the injective vanishes, hence the boundary is
surjective. Both maps commute with this boundary by normalization and
naturality of the Yoneda extension class. Induction on degree proves equality.
The transpose of the identity coefficient arrow is exactly the canonical
inverse-image comparison, yielding the asserted identity. -/
theorem spectralLimitCohomologyMap_id {X : TopCat.{u}} (f : X ⟶ X) (hf : f = 𝟙 X)
    (c : SiteCohomologyFamily (Opens.grothendieckTopology X)
      (Opens.grothendieckTopology X) (Opens.map f))
    (hc : @SiteCohomologyFamily.IsPullback _ _ _ _
      (Opens.grothendieckTopology X) (Opens.grothendieckTopology X)
      (Opens.map f) inferInstance
      (@Adjunction.left_adjoint_additive _ _ _ _ _ _ _ _
        (sheafAdjunctionContinuous (Opens.map f) AddCommGrpCat.{u}
          (Opens.grothendieckTopology X) (Opens.grothendieckTopology X))
        (Functor.additive_of_preserves_binary_products _))
      inferInstance inferInstance c)
    {A : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}
    (α : A ⟶ (pushforward AddCommGrpCat.{u} f).obj A)
    (hα : ∀ (U : Opens X) (s : A.obj.obj (op U)),
      HEq ((α.hom.app (op U)).hom s) s) (q : ℕ) :
    spectralLimitCohomologyMap f c α q = 𝟙 _ := by sorry

end TopCat.Sheaf
