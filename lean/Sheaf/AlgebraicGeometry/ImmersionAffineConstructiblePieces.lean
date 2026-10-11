/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.Topology.Constructible

/-! # Affine constructible pieces of an immersed scheme

Source: literature/stacks-project/etale-cohomology.tex, Etale Cohomology, Lemma Tag 03S0,
proof, line 12049 (blueprint: lem-weil-pbc-immersion-affine-constructible-pieces).
-/

@[expose] public section

open CategoryTheory
open Topology
namespace AlgebraicGeometry

/--
An immersion into an affine scheme whose image is constructible admits a finite
partition by affine schemes mapping by immersions to pairwise disjoint locally
closed constructible pieces.
Source: literature/stacks-project/etale-cohomology.tex, Etale Cohomology, Lemma Tag 03S0,
proof, line 12049 (blueprint: lem-weil-pbc-immersion-affine-constructible-pieces).

Proof (the six steps of the node):
1. Choose an isomorphism `X ≅ Spec A` using `def-pc-scheme` and
   `def-weil-affine-spectrum`. It and its inverse are open immersions
   (`def-weil-open-immersion`), hence immersions (`def-weil-closed-immersion`).
   Composition preserves immersions (`lem-weil-pbc-proper-fp-permanence`, clause (e)).
   The underlying homeomorphism preserves constructibility, local closedness,
   disjointness and unions (`def-weil-constructible-subset`,
   `def-weil-locally-closed-subset`), so it suffices to treat `X = Spec A`.
2. Write `E` as a finite union of basic sets `D(f) ∩ V(g₁, ..., gₙ)` using
   `lem-weil-pbc-affine-constructible-basic-union`. Refine to finitely many pairwise
   disjoint basic sets `Eₖ` using `lem-weil-pbc-affine-basic-sets-disjoint-refinement`.
   The index set may be empty.
3. For each piece put `Jₖ = (g₁, ..., gₙ)`, `Rₖ = (A/Jₖ)[1/f]`, and `Wₖ = Spec Rₖ`.
   The induced map `wₖ : Wₖ ⟶ X` is an immersion with image `Eₖ` by
   `lem-weil-pbc-basic-subset-immersion-image`.
4. Set `Zₖ = Z ×_X Wₖ` (`def-pc-fibre-product`) with projections `κₖ : Zₖ ⟶ Z`
   and `qₖ : Zₖ ⟶ Wₖ`. Both are immersions, being base changes of `wₖ` and `ι`
   (`lem-weil-pbc-immersion-base-change-lft`, clause (1)), and `κₖ ≫ ι = qₖ ≫ wₖ`.
5. By `lem-weil-pbc-base-change-image`, the image of `qₖ` is `wₖ⁻¹(E) = Wₖ`,
   since `Eₖ ⊆ E`. Thus `qₖ` is a closed immersion by
   `lem-weil-pbc-immersion-closed-image-closed-immersion`. Its target is affine
   (`def-weil-affine-spectrum`), so `Zₖ` is affine by
   `lem-weil-pbc-closed-immersion-affine-cover-criterion`, clause (1).
6. The composite `κₖ ≫ ι = qₖ ≫ wₖ` is an immersion by
   `lem-weil-pbc-proper-fp-permanence`, clause (e), with image `wₖ(Wₖ) = Eₖ`.
   Each basic set is locally closed (`def-weil-locally-closed-subset`) and constructible
   (`lem-weil-pbc-affine-constructible-basic-union`). Step 2 gives disjointness and
   union `E`, and step 5 gives affineness, as required.
-/
theorem exists_finite_affine_immersion_constructible_pieces
    {X Z : Scheme} (hX : IsAffine X) (ι : Z ⟶ X) [IsImmersion ι]
    (E : Set X) (hE : E = Set.range ι) (hEc : IsConstructible E) :
    ∃ (K : Type) (_ : Fintype K) (Zk : K → Scheme)
      (κ : ∀ k, Zk k ⟶ Z) (Ek : K → Set X),
      (∀ k, IsAffine (Zk k)) ∧
      (∀ k, IsImmersion (κ k)) ∧
      (∀ k, IsImmersion (κ k ≫ ι)) ∧
      (∀ k, Set.range (κ k ≫ ι) = Ek k) ∧
      (∀ k, IsLocallyClosed (Ek k)) ∧
      (∀ k, IsConstructible (Ek k)) ∧
      (Set.PairwiseDisjoint Set.univ Ek) ∧
      E = ⋃ k, Ek k := by
  sorry

end AlgebraicGeometry
