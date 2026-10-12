/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Mathlib.Topology.Sheaves.Abelian
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
/-! # Open embeddings and injective sheaf pullback

Source: Stacks Project, Tags 03DI and 03DJ.
-/
@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
/-- Pullback of abelian sheaves along an open embedding preserves injectives.
Source: Stacks Project, Tags 03DI and 03DJ.

Proof: Extension by zero along an open embedding is left adjoint to sheaf pullback.
On abelian sheaves it is constructed by left Kan extension followed by sheafification.
Both left Kan extension and sheafification preserve monomorphisms in this situation,
so the adjunction criterion
`Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms`
applies.
(blueprint: lem-pc-open-embedding-sheaf-pullback-injectives) -/
theorem Topology.isOpenEmbedding_sheafPullback_preservesInjectiveObjects
    {X Y : TopCat.{u}} (f : X ⟶ Y) (hf : Topology.IsOpenEmbedding f) :
    (TopCat.Sheaf.pullback AddCommGrpCat.{u} f).PreservesInjectiveObjects := by sorry
