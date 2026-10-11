/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective

/-!
# Functorial K-injective resolutions with injective terms

Source: Stacks Project, Theorem 19.12.6 (Tag 079P), including the injective-term clause
(blueprint: lem-pur-kinjective-degreewise-existence).
-/

@[expose] public section

universe w v u

open CategoryTheory

namespace CochainComplex

/-- In a Grothendieck abelian category, there is a functorial termwise monomorphic
quasi-isomorphism to a K-injective complex whose terms are all injective.
Source: Stacks Project, Theorem 19.12.6 (Tag 079P)
(blueprint: lem-pur-kinjective-degreewise-existence).

Proof plan from the node:
1. `lem-pur-kinjective-functorial-homotopies` gives the functor M with a termwise monomorphic
   quasi-isomorphism from the identity, killing maps from a chosen set of bounded-above
   acyclic complexes up to homotopy.
2. `lem-pur-kinjective-functorial-injective` gives the functor N with a termwise monomorphic
   quasi-isomorphism and factorizations through injective subobjects in each degree.
3. `lem-pur-kinjective-characterize-injective` gives the generator lifting test for injectivity;
   `prop-pur-kinjective-objects-small` ensures maps factor through earlier transfinite stages.
4. `lem-pur-kinjective-characterize-K-injective` tests K-injectivity using injective terms and
   null-homotopy of maps from bounded-above acyclic complexes of bounded size.
5. Choose an infinite cardinal kappa using
   `lem-pur-kinjective-acyclic-quotient-complexes-bounded-size`. Its two clauses persist on
   enlargement. Choose representatives of the bounded-above acyclic complexes with terms of
   size at most kappa using `lem-pur-kinjective-set-iso-classes-bounded-size`, and use them for M.
   Iterate T_0 = id, T_(gamma+1) = N composed with M composed with T_gamma, and take termwise
   colimits at limits. The transition maps are termwise monomorphic quasi-isomorphisms; AB5
   preserves these properties at limits. Fix a generator U and take alpha of cofinality greater
   than max(kappa, |U|), in particular uncountable. Set I = T_alpha with its natural map eta.
   A map from a subobject of U into a term of I factors through an earlier stage by smallness,
   hence through an injective subobject supplied by N at the next stage. It extends to U, so the
   generator lifting test makes every term injective. For a bounded-above acyclic complex P
   whose terms have size at most kappa, each component of a map P to I factors through an
   earlier stage. Uncountable cofinality gives one stage for all integer degrees; monomorphic
   transitions ensure compatibility with differentials. The next application of M kills this
   map up to homotopy. The K-injective criterion now applies. The construction throughout is
   functorial and eta remains a termwise monomorphic quasi-isomorphism. -/
theorem exists_functorial_kInjective_resolution_with_injective_terms
    (C : Type u) [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C] :
    ∃ (I : CochainComplex C ℤ ⥤ CochainComplex C ℤ)
      (η : 𝟭 (CochainComplex C ℤ) ⟶ I),
      ∀ (K : CochainComplex C ℤ),
        (∀ (n : ℤ), Mono ((η.app K).f n)) ∧
        QuasiIso (η.app K) ∧
        IsKInjective (I.obj K) ∧
        (∀ (n : ℤ), Injective ((I.obj K).X n)) := by
  sorry

end CochainComplex
