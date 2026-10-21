/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NP
-/
module

public import Mathlib.CategoryTheory.Action.Continuous
public import Mathlib.CategoryTheory.InducedCategory
public import Mathlib.Topology.Algebra.OpenSubgroup

/-! # The open-orbit category of a topological group

Source: Bhatt--Scholze, Proposition 7.1.5, printed p. 64.
(blueprint: def-sfb-open-orbit-functor)
-/

@[expose] public noncomputable section

set_option autoImplicit false
universe u

open CategoryTheory

namespace TopologicalGroup

/-- Identity forgetful functor needed by Mathlib's continuous-action interface for TopCat.
Source: Bhatt--Scholze, Proposition 7.1.5, p. 64.
(blueprint: def-sfb-open-orbit-functor) -/
@[instance_reducible]
def topCatIdentityForget : HasForget₂ TopCat.{u} TopCat.{u} where
  forget₂ := 𝟭 _

attribute [scoped instance] topCatIdentityForget

variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The discrete continuous action on the left cosets of an open subgroup.
Source: Bhatt--Scholze, Proposition 7.1.5, p. 64.
(blueprint: def-sfb-open-orbit-functor) -/
def openOrbitAction (U : OpenSubgroup G) : DiscreteContAction TopCat.{u} G :=
  ⟨⟨{ V := TopCat.of (G ⧸ U.toSubgroup)
      ρ :=
        { toFun := fun g => TopCat.ofHom ⟨fun x => g • x, continuous_const_smul g⟩
          map_one' := ConcreteCategory.hom_ext _ _ (fun x => one_smul G x)
          map_mul' := fun g h =>
            ConcreteCategory.hom_ext _ _ (fun x => mul_smul g h x) } },
     inferInstanceAs (ContinuousSMul G (G ⧸ U.toSubgroup))⟩,
   inferInstanceAs (DiscreteTopology (G ⧸ U.toSubgroup))⟩

/-- The small category indexed by open subgroups, with every equivariant map of coset sets.
Its induced-category construction uses Mathlib's category axioms without restricting arrows.
Source: Bhatt--Scholze, Proposition 7.1.5, p. 64.
(blueprint: def-sfb-open-orbit-functor) -/
abbrev OpenOrbitCategory :=
  InducedCategory (DiscreteContAction TopCat.{u} G) (openOrbitAction G)

/-- The canonical inclusion of the open-orbit category into all discrete continuous actions.
Source: Bhatt--Scholze, Proposition 7.1.5, p. 64.
(blueprint: def-sfb-open-orbit-functor) -/
def openOrbitInclusion : OpenOrbitCategory G ⥤ DiscreteContAction TopCat.{u} G :=
  inducedFunctor (openOrbitAction G)

/-- The underlying-set functor on all discrete continuous left actions.
Source: Bhatt--Scholze, Proposition 7.1.5, p. 64.
(blueprint: def-sfb-open-orbit-functor) -/
def discreteActionForget : DiscreteContAction TopCat.{u} G ⥤ Type u :=
  forget (DiscreteContAction TopCat.{u} G)

/-- The orbit underlying-set functor, definitionally the restriction of the full forgetful functor.
Source: Bhatt--Scholze, Proposition 7.1.5, p. 64.
(blueprint: def-sfb-open-orbit-functor) -/
def openOrbitForget : OpenOrbitCategory G ⥤ Type u :=
  openOrbitInclusion G ⋙ discreteActionForget G

end TopologicalGroup
