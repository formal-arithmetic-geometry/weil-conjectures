/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-!
# Constant pullback composition coherence

Source: Stacks Project, sites.tex, Tag 03CB; cohomology.tex, Tag 01F8.
(blueprint: lem-weil-pbc-constant-pullback-composition-coherence)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

open AlgebraicGeometry

namespace AlgebraicGeometry.Etale

/-- Constant-sheaf comparison morphisms commute with inverse-image composition.
Source: Stacks Project, sites.tex, Tag 03CB (composition of inverse images), and
cohomology.tex, Tag 01F8, applied to the constant sheaf.

Proof: the constant-sheaf comparisons are the unique left-adjoint comparisons for
constant sheaf followed by inverse image, both left adjoint to global sections.
The comparison upperStarComp is obtained by conjugating the composition comparison
for direct images. That comparison on sections over the terminal object is the
canonical pullback-pasting identification. Thus both displayed maps have the same
adjoint, namely the identity of the constant coefficient object followed by the
adjunction unit for the composite. Uniqueness under the adjunction gives equality.
This is an equality of sheaf morphisms, before applying cohomology in any degree.
(blueprint: lem-weil-pbc-constant-pullback-composition-coherence)
-/
theorem constantPullbackCompositionCoherence {X Y Z : Scheme.{u}}
    (u : X ⟶ Y) (v : Y ⟶ Z) (M : AddCommGrpCat.{u + 1}) :
    ((Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} (u ≫ v)).inv.app M) ≫
        (upperStarComp AddCommGrpCat.{u + 1} u v).hom.app
          ((constantSheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1}).obj M) =
      (Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} u).inv.app M ≫
        ((u)^*[AddCommGrpCat.{u + 1}]).map
          ((Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} v).inv.app M) := by sorry

end AlgebraicGeometry.Etale
