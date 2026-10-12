/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance

/-!
# Constant pullback identity coherence

Source: Stacks Project, sites.tex, Tag 03CB; cohomology.tex, Tag 01F8.
(blueprint: lem-weil-pbc-constant-pullback-identity-coherence)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

open AlgebraicGeometry

namespace AlgebraicGeometry.Etale

/-- Constant-sheaf comparison for identity inverse image is the inverse of upperStarId.
Source: Stacks Project, sites.tex, Tag 03CB, and cohomology.tex, Tag 01F8.

Proof: constantSheaf followed by inverse image of the identity is left adjoint to
sections composed with identity direct image. Transport along lowerStarId identifies
this adjunction with constantSheaf adjoint to sections. The definition of upperStarId
is the conjugate of the inverse of lowerStarId, while upperStarConstantSheafIso is
uniqueness of the same left adjoint. Hence their composite is the identity comparison,
by uniqueness of left-adjoint isomorphisms compatible with the adjunction units.
Taking its component at M gives the displayed equality of sheaf morphisms.
(blueprint: lem-weil-pbc-constant-pullback-identity-coherence)
-/
theorem constantPullbackIdentityCoherence (Z : Scheme.{u}) (M : AddCommGrpCat.{u + 1}) :
    (Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} (𝟙 Z)).inv.app M ≫
        (upperStarId AddCommGrpCat.{u + 1} Z).hom.app
          ((constantSheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1}).obj M) = 𝟙 _ := by sorry

end AlgebraicGeometry.Etale
