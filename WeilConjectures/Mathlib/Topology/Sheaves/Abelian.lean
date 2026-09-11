/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.Topology.Sheaves.Abelian
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Pullback
public import WeilConjectures.Mathlib.Topology.Sheaves.Stalks

/-!
# Exactness of the pullback and of the pushforward of abelian sheaves on a topological space

The pullback of sheaves of abelian groups along a continuous map of topological spaces is
exact: it preserves finite colimits because it is a left adjoint (this is
`CategoryTheory.Functor.preservesFiniteColimits_sheafPullback`), and it preserves finite
limits because `TopologicalSpace.Opens.map f` is representably flat
(`TopologicalSpace.Opens.preservesFiniteLimits_sheafPullback`).

The pushforward of sheaves of abelian groups along a *closed embedding* is exact as well
(`TopCat.Sheaf.preservesFiniteColimits_pushforwardAb`): exactness of a short complex of
sheaves can be checked on stalks, the stalk of a pushforward at a point of the image is the
corresponding stalk upstairs, and its stalk at a point outside the (closed) image vanishes.

Mathlib proves the latter for an arbitrary concrete coefficient category over small sites,
but that instance is not found in practice: the metavariables for the concreteness data
make the instance search diverge. This file records the specialisation to `AddCommGrpCat`
over the sites of open subsets of topological spaces, which is what is needed for sheaf
cohomology.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace TopologicalSpace.Opens

set_option maxHeartbeats 1000000 in
-- Elaborating the underlying left Kan extension is expensive; see the module docstring.
attribute [local instance] reflectsLimits_of_reflectsIsomorphisms in
/-- The pullback of sheaves of abelian groups along a continuous map is left exact. -/
instance preservesFiniteLimits_sheafPullback {X Y : TopCat.{u}} (f : X ⟶ Y) :
    PreservesFiniteLimits ((Opens.map f).sheafPullback AddCommGrpCat.{u}
      (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)) := by
  apply Functor.sheafPullbackConstruction.preservesFiniteLimits

end TopologicalSpace.Opens

namespace TopCat.Sheaf

open TopologicalSpace Topology

variable {X Y : TopCat.{u}} (f : X ⟶ Y)

/-- The pushforward of sheaves of abelian groups along a continuous map of topological
spaces. This is `CategoryTheory.Functor.sheafPushforwardContinuous` for
`TopologicalSpace.Opens.map f`, with source and target written as categories of sheaves on
topological spaces. -/
noncomputable def pushforwardAb : Sheaf AddCommGrpCat.{u} X ⥤ Sheaf AddCommGrpCat.{u} Y :=
  (Opens.map f).sheafPushforwardContinuous AddCommGrpCat.{u}
    (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)

instance : (pushforwardAb f).Additive where
  map_add := rfl

/-- The underlying presheaf of the pushforward of a sheaf is the pushforward of its
underlying presheaf. -/
noncomputable def pushforwardAbCompForgetIso :
    pushforwardAb f ⋙ forget AddCommGrpCat.{u} Y ≅
      forget AddCommGrpCat.{u} X ⋙ Presheaf.pushforward AddCommGrpCat.{u} f :=
  Iso.refl _

/-- The pushforward of sheaves of abelian groups along `f`, composed with the stalk functor
at a point `f x` in the image of `f`, is the stalk functor at `x`. -/
noncomputable def pushforwardAbCompStalkFunctorIso (hf : IsInducing f) (x : X) :
    pushforwardAb f ⋙ forget AddCommGrpCat.{u} Y ⋙
        Presheaf.stalkFunctor AddCommGrpCat.{u} (f x) ≅
      forget AddCommGrpCat.{u} X ⋙ Presheaf.stalkFunctor AddCommGrpCat.{u} x :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (pushforwardAbCompForgetIso f)
      (Presheaf.stalkFunctor AddCommGrpCat.{u} (f x)) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (forget AddCommGrpCat.{u} X)
      (Presheaf.pushforwardCompStalkFunctorIso AddCommGrpCat.{u} hf x)

/-- The pushforward of sheaves of abelian groups along a closed embedding is exact: its
stalk at a point in the image of `f` is the corresponding stalk upstairs, and its stalk at
a point outside the (closed) image vanishes. -/
lemma preservesFiniteColimits_pushforwardAb (hf : IsClosedEmbedding f) :
    Limits.PreservesFiniteColimits (pushforwardAb f) := by
  have key : ∀ S : ShortComplex (Sheaf AddCommGrpCat.{u} X), S.Exact →
      (S.map (pushforwardAb f)).Exact := by
    intro S hS
    rw [exact_iff_stalkFunctor_map_exact] at hS ⊢
    intro y
    by_cases hy : y ∈ Set.range f
    · obtain ⟨x, rfl⟩ := hy
      exact ShortComplex.exact_of_iso
        (ShortComplex.mapNatIso S (pushforwardAbCompStalkFunctorIso f hf.isInducing x)).symm (hS x)
    · exact ShortComplex.exact_of_isZero_X₂ _
        (isZero_stalk_pushforward_of_notMem_range hf.isClosed_range _ hy)
  have h : Limits.PreservesFiniteLimits (pushforwardAb f) ∧
      Limits.PreservesFiniteColimits (pushforwardAb f) :=
    ((Functor.exact_tfae _).out 1 3).mp key
  exact h.2

/-- The pushforward of sheaves of abelian groups along a closed embedding is right exact. -/
lemma preservesFiniteColimits_sheafPushforwardContinuous (hf : IsClosedEmbedding f) :
    Limits.PreservesFiniteColimits ((Opens.map f).sheafPushforwardContinuous AddCommGrpCat.{u}
      (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)) :=
  preservesFiniteColimits_pushforwardAb f hf

end TopCat.Sheaf
