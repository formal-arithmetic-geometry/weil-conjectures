/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Surjectivity of spectra after base change

Source: Stacks Project, Algebra, Lemma 10.30.3 (Tag 00FI), final assertion
(blueprint: lem-weil-pbc-spec-surjective-base-change).
-/

universe u

open scoped TensorProduct

namespace AlgebraicGeometry

/-- Surjectivity of an affine spectrum map persists after arbitrary ring base change.
Source: Stacks Project, Algebra, Tag 00FI, final assertion
(blueprint: lem-weil-pbc-spec-surjective-base-change).

Proof:
1. For a prime `p'` of `R'`, let `p` be its inverse image in `R`. Surjectivity makes
   `S ⊗[R] κ(p)` nonzero, by lem-weil-pbc-prime-in-image-iff-fibre-ring-nonzero.
   The same lemma reduces the conclusion to nonvanishing of the fibre at `p'`.
2. Localizing and quotienting gives the field inclusion `κ(p) → κ(p')`
   (def-weil-pbc-localization-at-prime). Its composite from `R` agrees with the map
   through `R'`, since both send an element to its residue class.
3. Tensor symmetry and two applications of lem-weil-pbc-tensor-cancel-base-change
   identify that fibre with `κ(p') ⊗[κ(p)] (S ⊗[R] κ(p))`.
4. A basis containing `1` gives a linear retraction `κ(p') → κ(p)` preserving `1`.
   Tensoring the retraction with the identity sends `1 ⊗ 1` to the nonzero unit
   of the original fibre. Thus the new fibre is nonzero and `p'` is in the image.
   As `p'` was arbitrary, the base-changed spectrum map is surjective. -/
theorem Spec.map_surjective_baseChange
    {R S R' : Type u} [CommRing R] [CommRing S] [CommRing R']
    [Algebra R S] [Algebra R R']
    (h : Surjective (Spec.map (CommRingCat.ofHom (algebraMap R S)))) :
    Surjective (Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeLeftRingHom : R' →+* R' ⊗[R] S))) := by
  sorry

end AlgebraicGeometry
