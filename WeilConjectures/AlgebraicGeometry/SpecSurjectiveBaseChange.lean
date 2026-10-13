/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.RingTheory.TensorProduct.Basic

import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Surjectivity of spectra after base change

Source: Stacks Project, Algebra, Lemma 10.30.3 (Tag 00FI), final assertion
(blueprint: lem-weil-pbc-spec-surjective-base-change).
-/

@[expose] public section

universe u

open scoped TensorProduct

namespace AlgebraicGeometry

/-- Surjectivity of an affine spectrum map persists after arbitrary ring base change.
Source: Stacks Project, Algebra, Tag 00FI, final assertion
(blueprint: lem-weil-pbc-spec-surjective-base-change).

Proof:
1. Regard the given surjectivity as an instance. Surjectivity is stable under
   scheme base change (Stacks Tag 01S1), so the first projection from
   `Spec R' ×[Spec R] Spec S` to `Spec R'` is surjective.
2. The affine pullback isomorphism `pullbackSpecIso R R' S` identifies this
   pullback with `Spec (R' ⊗[R] S)` (Stacks Tags 01I4 and 01JQ).
   Its inverse followed by the first projection is the required spectrum map,
   by `pullbackSpecIso_inv_fst R R' S`.
3. An isomorphism and a composite of surjective scheme morphisms are surjective.
   Rewrite by the projection identity and infer these instances. -/
theorem Spec.map_surjective_baseChange
    {R S R' : Type u} [CommRing R] [CommRing S] [CommRing R']
    [Algebra R S] [Algebra R R']
    (h : Surjective (Spec.map (CommRingCat.ofHom (algebraMap R S)))) :
    Surjective (Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeLeftRingHom : R' →+* R' ⊗[R] S))) := by
  -- Identify the affine base change with the scheme pullback.
  let := h
  rw [← pullbackSpecIso_inv_fst R R' S]
  infer_instance

end AlgebraicGeometry
