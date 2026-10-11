/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
module

public import Sheaf.AlgebraicGeometry.EtaleSheaves

/-!
# Pullback of finite locally constant abelian etale sheaves

Source: Stacks Project, Tags 095A, 03Q1 (3), and 03CB
(blueprint: lem-weil-pbc-pullback-finite-locally-constant).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- Pullback along a composite agrees with iterated pullback, and preserves finite local
constancy of the underlying sheaf of sets. Source: Stacks Project, Tags 095A, 03Q1 (3),
and 03CB (blueprint: lem-weil-pbc-pullback-finite-locally-constant).

Proof:
1. The base-change functors define morphisms of small etale sites. Their composition
identifies composite and iterated inverse images, by
`lem-weil-pbc-inverse-image-composition` (Tag 03CB).
2. Choose an etale cover trivializing `f⁻¹ F`. Pull it back along `g`; the resulting maps
are etale and jointly surjective by `lem-weil-pbc-etale-covering-base-change`.
On each member, `lem-weil-pbc-etale-inverse-image-restriction` and
`lem-weil-pbc-inverse-image-composition` identify the restriction of the pullback with
pullback of the original restriction. By
`lem-weil-pbc-etale-inverse-image-algebraic-structures`, forgetting the abelian structure
commutes with inverse image. By `lem-weil-pbc-sets-etale-inverse-image-constant-sheaf`,
the pullback of the constant underlying sheaf is constant. This proves local constancy.
By `lem-weil-pbc-inverse-image-stalk-germ` (Tag 03Q1 (3)), each geometric stalk of the
pullback is the stalk at its image point, hence is finite, as required by
`def-weil-pbc-etale-sheaves`.
3. Transport finite local constancy across the composition isomorphism of step 1 to
obtain the assertion for the composite inverse image. -/
theorem pullback_finite_locally_constant {T Y Y' : Scheme.{u}}
    (g : Y' ⟶ Y) (f : Y ⟶ T) (F : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : IsFiniteLocallyConstantEtaleSheafOfSets
      ((sheafCompose Y.smallEtaleTopology
        (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj
        ((Etale.upperStar AddCommGrpCat.{u + 1} f).obj F))) :
    Nonempty (((Etale.upperStar AddCommGrpCat.{u + 1} (g ≫ f)).obj F) ≅
      ((Etale.upperStar AddCommGrpCat.{u + 1} g).obj
        ((Etale.upperStar AddCommGrpCat.{u + 1} f).obj F))) ∧
    IsFiniteLocallyConstantEtaleSheafOfSets
      ((sheafCompose Y'.smallEtaleTopology
        (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj
        ((Etale.upperStar AddCommGrpCat.{u + 1} (g ≫ f)).obj F)) := by
  sorry

end AlgebraicGeometry.Scheme
