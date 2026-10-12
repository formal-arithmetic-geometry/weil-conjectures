/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K2
-/
module

public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
import Sheaf.CategoryTheory.Adjunction.LiftedCommGrpBranch
import Sheaf.CategoryTheory.SheavesAlgebraicStructuresAbelian

/-!
# Underlying sets of abelian inverse image

Source: Stacks Project, Sites, Section 00YR and Proposition 00YV (2), and
Modules on Sites, proof of Lemma 04JC
(blueprint: lem-weil-pbc-site-pullback-abelian-underlying).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Functor.sheafPullbackConstruction

namespace CategoryTheory

/-- Source: Stacks Project, Sites, Section 00YR and Proposition 00YV (2), and
Modules on Sites, first paragraph of the proof of Lemma 04JC
(blueprint: lem-weil-pbc-site-pullback-abelian-underlying).

Proof: Identify abelian sheaves on both sites with commutative group objects in
sheaves of sets, using `sheavesAlgebraicStructuresAbelian`. Lift the set-valued
pullback-pushforward adjunction using `Adjunction.liftedCommGrpBranch`: finite
limit preservation implies finite product preservation, so the left lift has
underlying functor equal to set-valued pullback. The right lift is naturally
isomorphic to abelian pushforward: precomposition computes products sectionwise,
so its transported multiplication, unit and inverse are the original sectionwise
addition, zero and negation. Transport the lifted adjunction across the two
identifications. Both its left adjoint and the constructed abelian pullback are
left adjoint to abelian pushforward. Uniqueness of left adjoints gives a natural
isomorphism between them. Composing with the forgetful identifications gives the
asserted isomorphism of underlying sheaves, on objects and morphisms. -/
theorem sitePullback_abelian_underlying
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D) (U : C ⥤ D)
    [U.IsContinuous J K]
    [PreservesFiniteLimits (sheafPullback U (Type u) J K)] :
    Nonempty (sheafPullback U AddCommGrpCat.{u} J K ⋙
        sheafCompose K (forget AddCommGrpCat.{u}) ≅
      sheafCompose J (forget AddCommGrpCat.{u}) ⋙ sheafPullback U (Type u) J K) := by
  sorry

end CategoryTheory
