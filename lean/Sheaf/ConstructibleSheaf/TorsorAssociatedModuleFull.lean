/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
module

public import Sheaf.ConstructibleSheaf.TorsorAssociatedModule

/-!
# Fullness of the associated module functor

Source: Stacks Project, Tags 0DV5 (3), 0DV6, 0A3R, 04TR and 04TS.
(blueprint: lem-weil-pbc-torsor-associated-module-full)
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory Limits
namespace AlgebraicGeometry
open Etale

/-- Associated module sheaves on a connected torsor remember precisely the
intertwining maps of representations.
Source: Stacks Project, Tags 0DV5 (3), 0DV6, 0A3R, 04TR and 04TS.
(blueprint: lem-weil-pbc-torsor-associated-module-full)

Proof:
Pull a sheaf map back to the torsor and use evaluation at the diagonal to identify
both associated sheaves with constant module sheaves. On a nonempty connected
scheme a map between constant module sheaves is induced by a unique linear map
of values: the image of each constant section is locally constant and hence
constant, and arbitrary locally constant sections are locally constant sections
of this form. Commutation with the canonical descent isomorphism on each group
component of the double overlap says that the recovered linear map intertwines
the representation actions. Its pointwise map on equivariant sections descends
to the original sheaf map, since equality is detected by the etale surjective
cover. This proves fullness. The zero module and trivial group need no exception;
no finite-dimensionality is used. -/
theorem Scheme.GaloisCover.associatedModuleFunctor_full
    {V : Scheme.{u}} [ConnectedSpace V] (ℓ : ℕ) [Fact ℓ.Prime]
    (P : Type u) [Group P] [Finite P]
    (c : Scheme.GaloisCover (ULift.{u + 1} P) V) [ConnectedSpace c.P] :
    (c.associatedModuleFunctor ℓ).Full := by sorry

end AlgebraicGeometry
