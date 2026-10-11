/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
module

public import Mathlib.RingTheory.Smooth.Basic
public import Sheaf.RingTheory.CompleteIntersectionOverField

/-!
# Smooth algebras over fields are local complete intersections

Source: Stacks Project, Algebra, Lemma 10.137.4 (Tag 00T5)
(blueprint: lem-weil-pbc-smooth-over-field-local-complete-intersection).
-/

@[expose] public section

universe u v

namespace Algebra

/-- (blueprint: lem-weil-pbc-smooth-over-field-local-complete-intersection)
Stacks Project, Algebra, Lemma 10.137.4 (Tag 00T5): a smooth algebra over a field is a local
complete intersection, hence admits a principal-open cover with global complete intersection
localizations.

Proof following the ten steps of the DAG node:
1. Smoothness implies finite presentation and finite type. Pass to an algebraic closure using
   `lem-weil-pbc-smooth-ring-map-base-change-composition`; descend the local complete
   intersection conclusion by `lem-weil-pbc-lci-field-change`. Thus assume the field is
   algebraically closed.
2. Choose a polynomial presentation with finitely generated kernel `I`. Apply
   `lem-weil-pbc-smooth-localization-conormal-split` with localization element `1` to obtain
   a split injection from `I/I²` into the free module on the polynomial differentials.
3. For a maximal ideal of the algebra, its inverse image in the polynomial ring is generated
   by `xᵢ - aᵢ`: use `lem-weil-pbc-zariski-lemma` and
   `lem-weil-pbc-alg-closed-finite-extension-trivial` to identify the residue field with `k`.
4. Translate the coordinates and use `lem-weil-pbc-polynomial-ring-origin-regular-local`.
   The polynomial local ring is regular of dimension `n`. By
   `lem-weil-pbc-regular-local-cotangent-dimension`, the classes of `xᵢ - aᵢ` give a basis of
   its maximal ideal modulo its square.
5. First order Taylor expansion modulo the square of that maximal ideal identifies the
   differential of a kernel element with its class in the cotangent space. Check constants
   and variables, then sums and products by the Leibniz rule.
6. Tensor the split injection with the residue field. Its source identifies with `I/m'I`
   since `I²` is contained in `m'I`; the resulting map is injective.
7. Choose kernel elements representing a basis of `I/m'I`. By
   `lem-weil-pbc-nakayama-local-generators`, their images generate the localized kernel.
8. Their cotangent classes are independent. Extend them to a cotangent basis; Nakayama gives
   generators of the maximal ideal. By
   `lem-weil-pbc-regular-local-generators-regular-sequence`, these form a regular sequence.
   The initial segment generating the localized kernel is therefore regular as well.
9. Apply `lem-weil-pbc-lci-regular-sequence-global-complete-intersection` to find an element
   outside the chosen maximal ideal whose localization is a global complete intersection.
10. Choose such an element for every maximal ideal. Every prime lies in a maximal ideal,
    so these principal opens cover the spectrum. For the zero ring the spectrum and the
    family of maximal ideals are empty. Together with finite type, this is precisely
    `IsLocalCompleteIntersection`. -/
theorem isLocalCompleteIntersection_of_smooth (k : Type u) (S : Type v) [Field k]
    [CommRing S] [Algebra k S] [Smooth k S] : IsLocalCompleteIntersection k S := by
  sorry

end Algebra
