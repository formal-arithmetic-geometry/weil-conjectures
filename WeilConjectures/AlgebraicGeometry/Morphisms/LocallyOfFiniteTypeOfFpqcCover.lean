/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
import WeilConjectures.AlgebraicGeometry.FpqcLocalOnBaseCriterion

/-!
# Fpqc descent of local finite type

Source: Stacks Project, Descent, Lemma 02KX, the descent direction of Definition 02KO
(blueprint: lem-weil-pbc-fpqc-descend-locally-finite-type).
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- (blueprint: lem-weil-pbc-fpqc-descend-locally-finite-type) Stacks Project, Descent,
Lemma 02KX: if every base change along an fpqc covering is locally of finite type, so is `f`.

Proof outline, following the six steps of the node:
1. Local finite type is invariant under isomorphisms and Zariski local on the target, by
   `lem-weil-pbc-lft-pointwise-criterion` (01T2).
2. It is stable under base change by `lem-weil-pbc-lft-base-change` (01T4).
3. For a flat surjective map of affine schemes, the associated ring map is faithfully flat,
   by `lem-weil-pbc-flat-ring-map-iff-flat-affine` and
   `lem-weil-pbc-flat-surjective-spectrum-faithfully-flat`.
4. For an affine open of the source, its inverse image in the base change is the spectrum
   of the tensor product: use `lem-weil-pbc-open-preimage-fibre-product`,
   `lem-weil-pbc-cartesian-square-pasting`, and `lem-weil-pbc-fibre-product-affine-spectra`.
   The base-changed algebra is finite type by `lem-weil-pbc-lft-affine-pairs` (01T2).
5. Descend finite generation by `lem-weil-pbc-finite-type-descends-faithfully-flat` (00QP);
   the pointwise criterion then makes the original morphism locally of finite type.
6. Apply `lem-weil-pbc-fpqc-local-on-base-criterion` (02KP) to the given covering family,
   using the preceding locality, base-change stability, and affine descent checks. -/
theorem locallyOfFiniteType_of_fpqcCover
    {X S : Scheme.{u}} (f : X ⟶ S) {I : Type v} (S' : I → Scheme.{u})
    (g : ∀ i, S' i ⟶ S) (hcover : Presieve.ofArrows S' g ∈ Scheme.fpqcPrecoverage S)
    (h : ∀ i, LocallyOfFiniteType (pullback.snd f (g i))) :
    LocallyOfFiniteType f := by
  sorry

end AlgebraicGeometry
