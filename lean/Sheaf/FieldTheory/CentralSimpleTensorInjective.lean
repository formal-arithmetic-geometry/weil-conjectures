module

public import Mathlib.Algebra.BrauerGroup.Defs
public import Mathlib.Algebra.Azumaya.Defs

@[expose] public section

universe u

namespace Field

/-- Injectivity of the enveloping map for a finite-dimensional central simple algebra.

Proof: taking the opposite preserves finite dimension, centrality and simplicity.
Stacks Tag 074G therefore makes `A ⊗[K] Aᵐᵒᵖ` simple. The kernel of the unital
algebra homomorphism `a ⊗ op(b) ↦ (v ↦ a * v * b)` is a two-sided ideal, so it is
zero or the whole domain. It cannot be the whole domain: the map sends one to the
identity endomorphism of the nonzero algebra A, and that endomorphism is not zero
(evaluate it at one). Thus its kernel is zero. If two elements have the same image,
their difference belongs to this zero kernel, so the elements are equal.
Source: Stacks Project, Tag 074I, Lemma 11.4.10, proof; tensor simplicity in
Tag 074G, Lemma 11.4.8.
(blueprint: lem-sc-central-simple-tensor-end-injective). -/
theorem centralSimple_mulLeftRight_injective (K : Type u) [Field K] (A : CSA.{u, u} K) :
    Function.Injective (AlgHom.mulLeftRight K A) := by sorry

end Field
