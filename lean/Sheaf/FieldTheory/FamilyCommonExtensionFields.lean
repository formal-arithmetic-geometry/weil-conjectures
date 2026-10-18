/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q81
-/
module

public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs

import Mathlib.Algebra.Category.CommAlgCat.Basic
import Mathlib.RingTheory.Spectrum.Maximal.Basic
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Sheaf.TraceFormula.FamilyTensorNontrivial

/-!
# A common extension field for a small family

Source: Stacks Project, Limits, Tag 0CNJ, proof of `lemma-infinite-product-surjective`
(blueprint: lem-trf-family-common-extension-field).
-/

@[expose] public section

set_option autoImplicit false

universe u v w

namespace Field

/-- Every small family of field extensions of `k` embeds compatibly in one field over `k`.
Source: Stacks Project, Limits, Tag 0CNJ, proof of `lemma-infinite-product-surjective`
(blueprint: lem-trf-family-common-extension-field).

Proof: Form the coproduct `A` of the commutative `k`-algebras `L j`, using
[lem-weil-pbc-commutative-algebras-colimits-exist]. It is nontrivial by
[lem-trf-family-tensor-nontrivial], including the empty family, whose coproduct is `k`.
Choose a maximal ideal `I` of `A` using [lem-weil-common-extension-fields-maximal-ideal].
Its quotient `K = A/I` is a field by [lem-weil-common-extension-fields-quotient-field];
properness of the maximal ideal ensures nontriviality. Compose each coproduct map with
the quotient map to obtain the `k`-algebra homomorphisms `e j`. Their compatibility with
the structural maps is the algebra-homomorphism condition. Each map is injective because
a unital homomorphism from a field to a nontrivial ring has zero kernel. When the family
is empty there are no embeddings to specify, and `k` itself is a common extension. -/
theorem exists_family_common_extension (k : Type u) [Field k] (J : Type w)
    (L : J → Type v) [∀ j : J, Field (L j)] [∀ j : J, Algebra k (L j)] :
    ∃ (K : Type (max u v w)) (_ : Field K) (_ : Algebra k K)
      (e : ∀ j : J, L j →ₐ[k] K), ∀ j : J, Function.Injective (e j) := by
  sorry

end Field
