/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NM
-/
module

public import WeilConjectures.CategoryTheory.StageSystem.Preadditive
public import Mathlib.Order.DirectedInverseSystem

/-! # Faithful reflexive stage transitions give a directed Hom system

Source: blueprint filtered two-colimit model proof, paragraph "The colimit is filtered",
with the unnormalized faithful-reflexive variant of `StageSystem.Basic` and
`StageSystem.Preadditive` (blueprint: lem-pur-faithful-stage-hom-transport).
-/

@[expose] public section
set_option autoImplicit false

universe w u v

namespace CategoryTheory.StageSystem

/-- The common-stage Hom groups and the associator-conjugated transports form a directed
system of abelian groups. The existentially bundled maps are specified pointwise by `S.tr`,
so they are precisely the canonical transports, not arbitrary homomorphisms.
`DirectedSystem.map_self` gives reflexive transport equal to the identity and
`DirectedSystem.map_map` gives strict composition. There is no normalization or unitor
hypothesis, and the three universes are independent.

Source: blueprint filtered two-colimit model proof, "The colimit is filtered"; the
faithful-reflexive variant uses `StageSystem.Basic` (`tr`, `tr_tr`, `tr_injective`) and
`StageSystem.Preadditive` (`tr_add`, `tr_zero`).
Proof: (1) The Hom groups are abelian by `def-weil-preadditive-category`. Additivity of
transition functors and bilinearity of composition show that `S.tr` preserves sums;
preservation of zero follows by cancellation. (2) Expand two successive transports.
The cocycle at the target and its inverse at the source, followed by naturality of the
middle associator, identify their composite with the direct transport. (3) At repeated
indices this makes reflexive transport idempotent. Conjugation by the endpoint isomorphisms
and faithfulness of the reflexive functor make it injective. An injective idempotent is the
identity. (4) An upper bound of the two endpoint stages proves that the common-stage
subtype is nonempty; an upper bound of two common stages is again a common stage, proving
directedness. The two laws are exactly `DirectedSystem` from
`def-weil-directed-colimit-abelian-groups`. All constructions use the underlying
`StageSystem` of `def-sf-directed-common-stage-data` without requiring its additional
exact/shift structures (blueprint: lem-pur-faithful-stage-hom-transport). -/
theorem faithful_hom_transport {I : Type w} [Preorder I] [IsDirectedOrder I] [Nonempty I]
    {C : I → Type u} [∀ i : I, Category.{v} (C i)] (S : StageSystem C)
    [∀ i : I, Preadditive (C i)]
    [∀ (i j : I) (h : i ≤ j), (S.T h).Additive]
    [∀ i : I, (S.T (le_refl i)).Faithful] (A B : S.PairCategory) :
    Nonempty {m : I // A.stage ≤ m ∧ B.stage ≤ m} ∧
    IsDirectedOrder {m : I // A.stage ≤ m ∧ B.stage ≤ m} ∧
    ∃ t : ∀ (m n : {m : I // A.stage ≤ m ∧ B.stage ≤ m}), m ≤ n →
        (A.toStage m.2.1 ⟶ B.toStage m.2.2) →+
          (A.toStage n.2.1 ⟶ B.toStage n.2.2),
      (∀ (m n : {m : I // A.stage ≤ m ∧ B.stage ≤ m}) (h : m ≤ n)
        (f : A.toStage m.2.1 ⟶ B.toStage m.2.2), t m n h f = S.tr h f) ∧
      DirectedSystem
        (fun m : {m : I // A.stage ≤ m ∧ B.stage ≤ m} ↦
          A.toStage m.2.1 ⟶ B.toStage m.2.2)
        (fun {m n} h ↦ t m n h) := by
  let J := {m : I // A.stage ≤ m ∧ B.stage ≤ m}
  have hne : Nonempty J := by
    obtain ⟨m, hmA, hmB⟩ := exists_ge_ge A.stage B.stage
    exact ⟨⟨m, hmA, hmB⟩⟩
  have hdir : IsDirectedOrder J := by
    refine ⟨fun m n ↦ ?_⟩
    obtain ⟨p, hmp, hnp⟩ := exists_ge_ge m.val n.val
    exact ⟨⟨p, m.property.1.trans hmp, m.property.2.trans hmp⟩, hmp, hnp⟩
  let t : ∀ (m n : J), m ≤ n →
      (A.toStage m.property.1 ⟶ B.toStage m.property.2) →+
        (A.toStage n.property.1 ⟶ B.toStage n.property.2) := fun m n h ↦
    { toFun := S.tr h
      map_zero' := tr_zero (S := S) h
      map_add' := fun f g ↦ tr_add (S := S) h f g }
  refine ⟨hne, hdir, t, fun _ _ _ _ ↦ rfl, ?_⟩
  constructor
  · intro m f
    change S.tr (le_refl m.val) f = f
    apply (S.T (le_refl m.val)).map_injective
    apply (tr_injective (le_refl m.val)).mp
    exact tr_tr (S := S) (le_refl m.val) (le_refl m.val) f
  · intro p n m hmn hnp f
    exact tr_tr (S := S) hmn hnp f

end CategoryTheory.StageSystem
