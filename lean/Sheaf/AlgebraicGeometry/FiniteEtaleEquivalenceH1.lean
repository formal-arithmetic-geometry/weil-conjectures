/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
public import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
import WeilConjectures.CategoryTheory.Sites.Torsor
import WeilConjectures.ConstructibleSheaf.Defs

/-!
# Finite étale equivalence and first cohomology

Source: the categorical last step of Stacks Project Tag 0A5G, using Tags 03AJ and 03RV.
(blueprint: lem-weil-pbc-finite-etale-equivalence-h1)
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Etale

/-- Pullback equivalence on finite étale schemes implies comparison for finite constant H¹.
Source: Stacks Project Tag 0A5G, last paragraph; Tags 03AJ and 03RV provide the torsor
classification used there. Only the categorical implication is stated: there is no
henselian ring, proper morphism, closed fibre, or assumption on the image of `i`.
(blueprint: lem-weil-pbc-finite-etale-equivalence-h1)

Proof: Write F for finite étale base change along i. A torsor under the finite constant
abelian group M is a finite locally constant sheaf of sets: étale locally it is the
constant finite set M. By 03RV it is represented by a finite étale scheme P over Y,
with an M-action, surjective structure morphism, and the isomorphism
M × P → P ×_Y P expressing simple transitivity. Conversely these data give a sheaf
torsor. The classification of 03AJ is natural in pullback and coefficient isomorphisms.

Full faithfulness of F lifts isomorphisms of restricted torsors uniquely. Faithfulness
shows the lifts commute with every M-action map and are inverse, proving injectivity
on torsor isomorphism classes. To lift a torsor W over Y₀, choose its finite étale
representative P over Y by essential surjectivity. Lift each action map by fullness.
Faithfulness lifts the identity and addition equations; the maps for -m are inverses.
The simple-transitivity map is a map between finite étale Y-schemes (the finite disjoint
union of copies of P and P ×_Y P). Its restriction is an isomorphism, so F reflects that
it is an isomorphism. Finally the image U of P → Y is open since the map is étale, and
closed since it is finite. The inclusion U → Y is finite étale. Its restriction has
image all of Y₀ because W → Y₀ is surjective, so this restricted clopen inclusion is an
isomorphism. Reflection of isomorphisms makes U → Y an isomorphism, proving P → Y
surjective. Thus the lifted data form a torsor and give surjectivity on classes.

Transport this bijection through 03AJ. The natural isomorphism from the inverse image
of the constant sheaf M on Y to the constant sheaf M on Y₀ identifies the transported
map with H¹ of that isomorphism after cohomologyMap i. H¹ of an isomorphism is bijective,
so cohomologyMap i itself is bijective, with precisely its inverse-image coefficient
codomain. Empty bases and the trivial group cause no exception; the image and reflection
argument does not presume that i is surjective. -/
theorem bijective_cohomologyMap_one_of_finiteEtale_equivalence
    [(@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}).IsStableUnderBaseChange]
    {Y Y₀ : Scheme.{u}} (i : Y₀ ⟶ Y)
    (hFE : (MorphismProperty.Over.pullback (@IsFinite ⊓ @Etale) ⊤ i).IsEquivalence)
    (M : Type (u + 1)) [AddCommGroup M] [Finite M] :
    Function.Bijective (cohomologyMap i
      ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj (AddCommGrpCat.of M)) 1) := by
  sorry

end AlgebraicGeometry.Etale
