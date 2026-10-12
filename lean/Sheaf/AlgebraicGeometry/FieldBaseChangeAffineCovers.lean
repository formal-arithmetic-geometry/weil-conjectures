/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A2
-/
module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Matching affine covers under field extension

Source: Stacks Project, Tags 01JR, 01JQ and 01T0.
-/

@[expose] public section

universe z

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace AlgebraicGeometry

/-- A nonempty scheme locally of finite type over a field admits affine covers that
identify scalar extension chartwise with tensor products.
Source: Stacks Project, Tags 01JR, 01JQ and 01T0; blueprint
`sec-picard-framework/sk-thm-picard-rr/lem-pc-dim-base-change.md`, proof paragraph 2.

Proof: choose the affine basis cover of X. Each coordinate ring is a finite type
k-algebra because the structure morphism is locally of finite type. The inverse
images of the chart opens under the first pullback projection cover the pullback.
Restriction of a fibre product to an open (01JR) and the fibre product of affine
spectra (01JQ) identify these opens with Spec(A_i tensor_k K). The morphism
Spec K → Spec k is surjective (both spectra of fields have one point). Its base
change is surjective, so the pullback is nonempty when X is. Empty chart rings are
permitted; no integrality, separatedness, or dimension assumption is needed.
(blueprint: lem-pc-dim-base-change-affine-covers)
-/
theorem exists_field_baseChange_affine_covers
    (k K : Type z) [Field k] [Field K] [Algebra k K]
    {X : Scheme.{z}} (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] [Nonempty X] :
    let Y := pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K)))
    Nonempty Y ∧ ∃ (I : Type z) (A : I → Type z) (rings : ∀ i, CommRing (A i)),
      letI := rings
      ∃ (algebras : ∀ i, Algebra k (A i)),
        letI := algebras
        (∀ i, Algebra.FiniteType k (A i)) ∧
          ∃ (U : I → X.Opens) (V : I → Y.Opens),
            (⨆ i, U i) = ⊤ ∧ (⨆ i, V i) = ⊤ ∧
            Nonempty (∀ i, (U i : Scheme.{z}) ≅ Spec (.of (A i))) ∧
            Nonempty (∀ i, (V i : Scheme.{z}) ≅ Spec (.of (A i ⊗[k] K))) := by
  sorry

end AlgebraicGeometry
