/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
module

public import Mathlib.FieldTheory.Galois.Basic
public import Sheaf.AlgebraicGeometry.BaseChangeConventions
public import WeilConjectures.AlgebraicGeometry.Picard.Jacobian

/-!
# Descent of Galois-invariant closed subsets

Source: Stacks Project, Varieties, Tag 038B, Lemma `lemma-closed-fixed-by-Galois`,
and equation `equation-galois-action-base-change-kbar`
(blueprint: lem-weil-pbc-galois-invariant-closed-subset-descends).

The base change is the chosen fibre product, with `pullback.fst` as its projection to `X`.
The existing `specAlgEquivOver` and `baseChangeMap` give the contravariant Galois action.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A closed subset of a Galois base change, invariant under every Galois automorphism,
is the inverse image of a closed subset of the original scheme. The extension may be infinite.
Source: Stacks Project, Varieties, Tag 038B
(blueprint: lem-weil-pbc-galois-invariant-closed-subset-descends).

Proof:
1. Functoriality of `Spec` and the fibre product gives automorphisms `σ_X` over `X`,
   with inverse `(σ⁻¹)_X` and reversed composition (def-weil-affine-spectrum,
   def-pc-base-change). Image invariance therefore also gives inverse-image invariance.
2. On an affine open `U = Spec A` of `X`, the base change is `Spec (A ⊗[k] K)`;
   its action is `Spec (id_A ⊗ σ)` and its projection is induced by `a ↦ a ⊗ 1`
   (lem-weil-pbc-open-fibre-product, lem-weil-pbc-fibre-product-affine-spectra,
   lem-weil-pbc-algebra-tensor-map-ring-hom, def-pc-fibre-product, def-pc-scheme).
3. The restricted closed subset has a unique radical ideal `Ibar`. Invariance of its
   vanishing set implies invariance of `Ibar` under these ring automorphisms
   (lem-weil-pbc-zero-locus-eq-iff-radical-eq).
4. Write any `x ∈ Ibar` as a finite sum of pure tensors. Its coefficients lie in a finite
   Galois subextension `M/k` of `K/k` (lem-weil-pbc-finite-set-in-finite-galois-subextension).
   Its finite automorphism group `G` has fixed field `k` (lem-weil-pbc-finite-galois-fixed-field).
5. Every automorphism of `M/k` extends to `K/k`
   (lem-weil-pbc-normal-subextension-automorphism-extends), so all conjugates of `x` lie in
   `Ibar` after inclusion into `A ⊗[k] K`.
6. The monic product `P(T) = ∏ τ ∈ G, (T - τ(x))` vanishes at `x`. Its coefficients are
   invariant under `G` and hence lie in `A` (lem-weil-pbc-tensor-field-extension-galois-invariants).
7. All nonleading coefficients of `P` belong to `I = Ibar ∩ A`. The equation `P(x) = 0`
   shows that a positive power of `x` belongs to the extended ideal `I (A ⊗[k] K)`.
   Thus `Ibar` is its radical; the reverse inclusion follows from radicality of `Ibar`.
8. The inverse image of `V(I)` is therefore the given closed subset on this affine chart
   (lem-weil-pbc-zero-locus-eq-iff-radical-eq, def-weil-affine-spectrum).
9. The projection is surjective, being the base change of the surjective map of field spectra
   (def-weil-surjective-morphism, lem-weil-pbc-surjective-base-change).
10. Set `T = p(Tbar)`. Surjectivity identifies its restriction to every affine open with
    the closed set constructed in step 8. Affine opens cover `X` (def-pc-scheme), so `T`
    is closed, and the same local equalities show `p⁻¹(T) = Tbar` globally. -/
theorem exists_closed_subset_of_galois_invariant
    (k K : Type u) [Field k] [Field K] [Algebra k K] [IsGalois k K]
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    (Tbar : Set ↥(pullback (X ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))))
    (hclosed : IsClosed Tbar)
    (hinvariant : ∀ σ : K ≃ₐ[k] K,
      (baseChangeMap (X ↘ Spec (.of k)) (specAlgEquivOver σ)) '' Tbar = Tbar) :
    ∃ T : Set X, IsClosed T ∧
      (pullback.fst (X ↘ Spec (.of k))
        (Spec.map (CommRingCat.ofHom (algebraMap k K)))) ⁻¹' T = Tbar := by
  sorry

end AlgebraicGeometry
