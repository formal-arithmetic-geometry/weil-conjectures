/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q23
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.OpenImmersion

/-!
# Integral surjective refinements of fppf coverings

Source: Stacks Project, More on Morphisms, Tag 0CNZ, lemma-dominate-fppf-integral
(blueprint: lem-trf-fppf-integral-surjective-refinement).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- An fppf covering of any scheme admits an integral surjection with an open covering whose
members lift over the base to members of the given covering. The families are small in the
scheme universe. Empty schemes and empty covering families are permitted.

Source: Stacks Project, More on Morphisms, Tag 0CNZ, lemma-dominate-fppf-integral
(blueprint: lem-trf-fppf-integral-surjective-refinement).

Proof plan:
1. Apply `lem-trf-fppf-local-finite-free-refinement` (Tag 05WN) to obtain an open cover
   `X = ⋃ U_j`, surjective finite locally free maps `W_j → U_j`, open covers
   `W_j = ⋃ W_{j,k}`, and surjective finite locally free maps `T_{j,k} → W_{j,k}`
   whose composites to `X` factor through members of the original covering.
2. Use `lem-trf-integral-surjective-open-extension` (Tag 0CNX) to extend the maps
   `W_j → U_j` to integral surjections `Wbar_j → X`, and the maps
   `T_{j,k} → W_{j,k}` to integral surjections `Tbar_{j,k} → Wbar_j`, retaining the
   specified inverse images over the original opens.
3. Take the products `Tbar_j = ∏_k Tbar_{j,k}` over `Wbar_j` and `Y = ∏_j Tbar_j`
   over `X`. They exist by `lem-trf-affine-infinite-product-existence`, since integral
   maps are affine. The maps are integral and surjective by
   `lem-trf-infinite-product-integral`, `lem-trf-infinite-product-surjective`,
   `lem-trf-integral-morphism-composition`, and `lem-trf-surjective-morphism-composition`.
4. Pull back the opens `T_{j,k} ⊆ Tbar_{j,k}` to `Y`. For each point of `Y`, choose
   `j` with its image in `U_j` and then `k` with its image in `W_{j,k}`. This point
   belongs to the corresponding pulled-back open. The projection to `T_{j,k}` and
   the factorization in step 1 give its lift to some `Xi i`, over `X`.
5. For empty `X`, use its identity and the empty open cover. If `I` is empty,
   joint surjectivity forces `X` to be empty. No quasi-compactness or quasi-separatedness
   hypothesis, or finiteness or finite-presentation conclusion for `q`, is used.
-/
theorem exists_integral_surjective_fppf_refinement
    {X : Scheme.{u}} {I : Type u} (Xi : I → Scheme.{u})
    (f : (i : I) → Xi i ⟶ X)
    [hflat : ∀ i, Flat (f i)]
    [hlfp : ∀ i, LocallyOfFinitePresentation (f i)]
    (hjoint : ∀ x : X, ∃ i y, f i y = x) :
    ∃ (Y : Scheme.{u}) (q : Y ⟶ X),
      IsIntegralHom q ∧ Surjective q ∧
      ∃ (A : Type u) (W : A → Scheme.{u}) (j : (a : A) → W a ⟶ Y)
        (i : A → I) (h : (a : A) → W a ⟶ Xi (i a)),
        (∀ a, IsOpenImmersion (j a)) ∧
        (∀ y : Y, ∃ a w, j a w = y) ∧
        (∀ a, h a ≫ f (i a) = j a ≫ q) := by
  sorry

end AlgebraicGeometry
