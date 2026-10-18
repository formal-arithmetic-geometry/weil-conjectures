/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q02
-/
module

public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact

import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Kernels
import Sheaf.Algebra.Homology.SubcategoryRightResolution

/-!
# Replacement of complexes by objects of degree zero

Source: Stacks Project, Derived Categories, Tag 07K6, `lemma-replace-resolution`,
the uniformly bounded finite-degree specialization
(blueprint: lem-sf-degree-zero-complex-replacement).
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

/-- A uniformly bounded nonnegative degree function admitting embeddings into degree-zero
objects, bounded on binary direct sums by the maximum, and decreasing on cokernels as
specified below admits a degree-zero replacement of every integer-indexed cochain complex.

Source: Stacks Project, Derived Categories, Tag 07K6, `lemma-replace-resolution`
(blueprint: lem-sf-degree-zero-complex-replacement).

Proof:
1. Embed the zero object in a degree-zero object I. Apply the short-exact inequality
   to I → I → 0 to get d(0) = 0. Applying it to 0 → A → B for an isomorphism and its
   inverse shows that d is invariant under isomorphisms. If D = 0, use the identity
   of K. Otherwise let the prescribed class consist of the objects of degree zero.
2. Apply `lem-weil-pbc-subcategory-right-resolution-05T6` to the brutal lower truncation
   of K at zero. It gives a termwise monomorphic quasi-isomorphism σ to a complex M
   supported in nonnegative degrees with degree-zero terms. Splice M to the negative
   part of K, using d_K followed by σ at the boundary, obtaining α : K → J. The chain
   map equation follows from that for σ. Cohomology below degree -1 is unchanged;
   in degree -1 use that σ is mono; in degree zero its isomorphism on kernels identifies
   the incoming images; above zero use its quasi-isomorphism. Thus α is a quasi-isomorphism,
   and J has degree-zero terms in nonnegative degrees and degree at most D everywhere.
3. For a current complex C, choose a bad index n and an embedding j : Cⁿ → E with d(E) = 0.
   Set P = coker((j, -d_C) : Cⁿ → E ⊕ Cⁿ⁺¹), with projection q and maps u, v from the
   two summands. The relation j ≫ u = d_C ≫ v makes P the pushout of j and d_C.
   Replace terms n, n+1 by E, P; the changed differentials are d_C ≫ j, u, and the
   descended map g with q ≫ g = (0, d_C). The cokernel relation and cancellation of
   the epi q prove that consecutive differentials compose to zero. Components j, v
   and identities elsewhere define a chain map f : C → C'.
4. By `lem-weil-pbc-abelian-pushout-mono`, v is mono, so f is termwise mono.
   By `lem-weil-pbc-pushout-cokernel-iso`, its quotient complex has only two possibly
   nonzero terms, coker(j), coker(v), with an isomorphism as their differential.
   It is acyclic. The long exact sequence of
   `lem-weil-pbc-complex-ses-homology-long-exact` makes every Hʳ(f) an isomorphism.
5. The map (j, -d_C) is mono. The two degree inequalities yield
   d(P) ≤ max(d(Cⁿ) - 1, d(Cⁿ⁺¹)). Thus replacement makes term n degree zero,
   changes only term n+1 otherwise, and preserves the uniform bound D.
6. Give each bad index r weight r + d(Cʳ). Initially these weights are bounded above
   by D-1. At maximum weight ξ the attaining indices form a finite set I contained
   in [ξ-D, ξ-1]. Replace its smallest index n. No weight increases above ξ; n leaves
   I and only n+1 may enter it. Therefore the positive integer sum of ξ-r over r in I
   drops at least by one until no index attains ξ. This removes each maximum in
   finitely many replacements, after which either no bad terms remain or it decreases.
7. Organize these finite operations into rounds. Stop if no bad terms remain, including
   before the first round. Otherwise the maxima ξ_s satisfy ξ_s ≤ ξ_0-s. All changes
   during round s occur in terms and differential sources at most ξ_s, and transition
   components above ξ_s are identities. For every m, eventually ξ_s < m, so every
   right-hand tail is literally unchanged. No infinite colimit is used.
8. Take the eventual terms and differentials as L. Their square-zero equations hold
   in a common late round. The eventual components of the finite composites from J
   give a chain map β : J → L. A positive-degree stabilized term in degree r would
   have weight at least r+1, contradicting a late maximum below r+1. Hence all terms
   of L have degree zero. In the stopping case take the last complex and finite composite.
9. Fix r and choose a round after stabilization in degrees r-1, r, r+1. Both Hʳ(L)
   and Hʳ(β) are computed in that finite round, whose composite from J is a
   quasi-isomorphism by step 4. In the stopping case use the finite composite or identity.
   Thus β is a quasi-isomorphism. Compose α and β to obtain the required map from K.
-/
theorem exists_quasiIso_degree_zero_of_bounded_degree
    (C : Type u) [Category.{v} C] [Abelian C]
    (d : C → ℕ) (D : ℕ) (hbound : ∀ A : C, d A ≤ D)
    (hembed : ∀ A : C, ∃ (I : C) (j : A ⟶ I), Mono j ∧ d I = 0)
    (hsum : ∀ A B : C, d (biprod A B) ≤ max (d A) (d B))
    (hshort : ∀ S : ShortComplex C, S.ShortExact →
      d S.X₃ ≤ max (d S.X₁ - 1) (d S.X₂))
    (K : CochainComplex C ℤ) :
    ∃ (L : CochainComplex C ℤ) (f : K ⟶ L),
      QuasiIso f ∧ ∀ r : ℤ, d (L.X r) = 0 := by
  sorry

end CochainComplex
