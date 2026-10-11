/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Sheaf.RingTheory.RingPseudoCoherent

/-!
# Finite free models at a cohomological upper bound

Source: Stacks Project, More on Algebra, Lemma 15.66.5, Tag 064U
(blueprint: lem-pc-pseudo-coherent-bounded-finite-free-model).
-/

@[expose] public section

universe w v u

open CategoryTheory CategoryTheory.Limits

namespace DerivedCategory

/-- A pseudo-coherent object of `D(R)` with no cohomology above `b` admits a finite free
representative with no terms above `b`.
Source: Stacks Project, More on Algebra, Lemma 15.66.5, Tag 064U, final assertion
(blueprint: lem-pc-pseudo-coherent-bounded-finite-free-model).

Proof:
1. Pseudo-coherence supplies a bounded above finite projective representative. Replace it
   by a finite free complex, descending from its highest degree: choose projective
   complements in finite free modules, and insert identity differentials on the complements.
   The projection has a contractible kernel and is a quasi-isomorphism (Tag 064U).
2. The resulting representative has the same cohomology as `C`, so it has zero cohomology
   in each degree above `b`.
3. At a highest nonzero degree `n > b`, the preceding differential is surjective and splits
   because the top term is projective. Cancel the contractible two-term summand. The new
   top term is finite projective; apply the finite free replacement of step 1 to this
   shortened complex. Repeat for the finitely many degrees above `b`. If there are no
   terms above `b`, no cancellation is needed. Compose the resulting quasi-isomorphisms. -/
theorem exists_finiteFree_model_isStrictlyLE
    {R : Type u} [CommRing R] [HasDerivedCategory.{w} (ModuleCat.{v} R)]
    (C : DerivedCategory (ModuleCat.{v} R)) (b : ℤ) (hC : IsPseudoCoherent C)
    (hvan : ∀ i : ℤ, b < i → IsZero ((homologyFunctor (ModuleCat.{v} R) i).obj C)) :
    ∃ P : CochainComplex (ModuleCat.{v} R) ℤ,
      P.IsStrictlyLE b ∧
      (∀ i : ℤ, Module.Free R (P.X i) ∧ Module.Finite R (P.X i)) ∧
      Nonempty (Q.obj P ≅ C) := by
  sorry

end DerivedCategory
