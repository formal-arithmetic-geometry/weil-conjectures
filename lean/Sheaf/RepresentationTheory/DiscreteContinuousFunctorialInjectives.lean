/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF worker C1
-/
module

public import Sheaf.RepresentationTheory.DiscreteContinuousRep
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import Sheaf.CategoryTheory.AdjunctionTransferFunctorialInjectives
import Sheaf.GroupTheory.GroupAlgebraFunctorialInjectiveEmbeddings
import Sheaf.RepresentationTheory.OpenStabilizerAdjunction

/-!
# Functorial injective embeddings of discrete continuous representations

Source: Stacks Project, Injectives, Tag 04JF, Lemma 19.3.1
(blueprint: lem-exc-rg-discrete-modules-functorial-injective-embeddings).
-/

@[expose] public section

universe u v w

open CategoryTheory

namespace Rep

/-- (blueprint: lem-exc-rg-discrete-modules-functorial-injective-embeddings)
For any ring `R` and topological group `G`, the category of discrete continuous
representations has functorial injective embeddings. Source: Stacks Project,
Injectives, Tag 04JF, Lemma 19.3.1.

Proof: first use functorial injective embeddings for modules over the group ring `R[G]`
(`lem-exc-rg-group-algebra-functorial-injective-embeddings`). The fully faithful inclusion
of the open-stabilizer subcategory preserves monomorphisms and has the open-stabilizer
submodule functor as its right adjoint (`lem-exc-rg-open-stabilizer-adjoint`). Apply
`lem-exc-rg-adjoint-transfer-functorial-injectives` to these functors and the group-ring
embedding functor. It gives an endofunctor `J`, a natural transformation from the identity,
monic components, and injective values, as asserted. -/
theorem discreteContinuousRep_functorialInjectiveEmbeddings_of_topologicalGroup
    (R : Type u) [Ring R] (G : Type v) [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] :
    ∃ (J : DiscreteContinuousRep.{u, v, max u v w} R G ⥤
          DiscreteContinuousRep.{u, v, max u v w} R G)
      (j : 𝟭 (DiscreteContinuousRep.{u, v, max u v w} R G) ⟶ J),
      (∀ M, Mono (j.app M)) ∧ ∀ M, Injective (J.obj M) := by
  sorry

end Rep
