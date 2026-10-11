/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
import Mathlib.Algebra.Homology.Factorizations.CM5a

/-!
# Bounded-below complexes embed into complexes of injectives

Source: Stacks Project, Derived Categories, Lemma Tag 013K (part (3)),
using Lemma Tag 05T6 (blueprint: lem-weil-pbc-complex-injective-resolution-mono).
-/

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

/-- Every bounded-below cochain complex in an abelian category with enough injectives
admits a degreewise monomorphic quasi-isomorphism to a bounded-below complex of
injectives with the same lower bound.

Source: Stacks Project, Derived Categories, Lemma Tag 013K (part (3)),
specialized from Lemma Tag 05T6 (blueprint: lem-weil-pbc-complex-injective-resolution-mono).
Proof:
1. Apply `lem-weil-pbc-subcategory-right-resolution-05T6` (Tag 05T6(1)) with the subset
   of injective objects of `C` from `def-sp-injective-resolutions`.
2. The zero object is injective: every map into zero extends uniquely along a monomorphism.
   Enough injectives supplies an embedding of every object into an injective object,
   verifying the other hypothesis of Tag 05T6(1).
3. That lemma supplies a complex `I` of injectives and a quasi-isomorphism `α : K ⟶ I`,
   monomorphic in every degree, with `I.X n` zero for `n < a`. These are precisely the
   four conclusion clauses.
-/
theorem exists_mono_quasiIso_injective_boundedBelow
    (C : Type u) [Category.{v} C] [Abelian C] [EnoughInjectives C]
    (a : ℤ) (K : CochainComplex C ℤ)
    (hK : ∀ n : ℤ, n < a → IsZero (K.X n)) :
    ∃ (I : CochainComplex C ℤ) (α : K ⟶ I),
      (∀ n : ℤ, n < a → IsZero (I.X n)) ∧
      (∀ n : ℤ, Injective (I.X n)) ∧
      (∀ n : ℤ, Mono (α.f n)) ∧ QuasiIso α := by
  sorry

end CochainComplex
