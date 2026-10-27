/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C9
-/
module

public import Sheaf.Paper.FiniteProjectionExchangeData

/-! # Identity normalization of the finite compact projection -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.FiniteProjectionExchange
variable (A : Type (u + 1)) [CommRing A] [Finite A]

/-- The actual identity compactification projection is the identity under its unit maps.
Source: prop-sf-pf-coherence.proof.md, first paragraph.
(blueprint: lem-sf-finite-projection-identity-normalization).

Proof: expand the compactification projection for j=p=id. The canonical derived
identity comparisons transport the pull/push adjunction to the identity adjunction;
this follows on complex representatives from the ordinary identity adjunction, and
then from uniqueness of the derived comparison. The tensor comparison for id is
therefore the tensor of these identity comparisons. The counit-defined proper
projection becomes the identity by the triangle identity. The open inverse projection
has transpose eta tensor 1, so under the open identity unit it too becomes the identity.
The composite of the proper identity and the open identity is the identity. Expanding
identitySupport is exactly the direct-image identity comparison followed by the
extension identity comparison. Naturality moves its inverse at K across the tensor,
and the pullback identity on L cancels the remaining target comparison. These are
the four arrows in IdentityLaw, proving the stated normalization. -/
theorem identity_normalization (X : Scheme.{u}) (K L : Dcat A X) :
    IdentityLaw A X K L := by sorry

end AlgebraicGeometry.ProEtale.FiniteProjectionExchange
