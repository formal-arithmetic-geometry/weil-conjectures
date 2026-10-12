/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N1
-/
module

public import Sheaf.ConstructibleSheaf.TorsorAssociatedModule

/-!
# Gluing equivariant module sections

Source: Stacks Project, Tags 0DV5 (3), 0DV6, 0A3R, 04TR and 04TS.
(blueprint: lem-weil-pbc-torsor-equivariant-module-is-sheaf)
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory Limits Opposite
namespace AlgebraicGeometry.Scheme.GaloisCover

/-- Equivariant locally constant module sections satisfy etale descent.
Source: Stacks Project, sites.tex Tags 04TR and 04TS; etale-cohomology.tex Tag 0DV5 (3).
(blueprint: lem-weil-pbc-torsor-equivariant-module-is-sheaf)

Proof: Let a matching family of equivariant sections be given on an etale cover
of an etale object W. Base change this cover along the torsor to obtain an etale
surjective cover of W times_V c.P. Etale maps are open, so matching locally
constant functions on this cover glue uniquely to a locally constant function:
define its value at a point using any lift, with independence given by matching
on the fibre products. Surjectivity of the maps from the fibre products to the
corresponding products of geometric fibres gives independence for arbitrary
scheme points too. Openness gives local constancy of the glued function.
Apply the same uniqueness to the pullback by each group action and the function
obtained by applying the representation action. They agree on the cover by
local equivariance, hence agree globally. Gluing is linear since addition and
scalar multiplication are pointwise. Thus every matching family in the module
presheaf has a unique amalgamation, proving the module-valued sheaf condition. -/
theorem equivariantModulePresheaf_isSheaf
    {V : Scheme.{u}} (ℓ : ℕ) {P : Type u} [Group P] [Finite P]
    (c : Scheme.GaloisCover (ULift.{u + 1} P) V)
    (N : Rep.{u + 1} (ZMod ℓ) P) :
    Presheaf.IsSheaf V.smallEtaleTopology (c.equivariantModulePresheaf ℓ N) := by sorry

end AlgebraicGeometry.Scheme.GaloisCover
