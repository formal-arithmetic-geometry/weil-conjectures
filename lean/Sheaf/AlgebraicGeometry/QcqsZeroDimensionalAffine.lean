/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NB
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.Topology.KrullDimension
import Mathlib.RingTheory.Ideal.Maximal
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Sheaf.AlgebraicGeometry.ZeroDimensionalSpectrumProfinite
import Sheaf.AlgebraicGeometry.QuasiCompactOpenIntersection
import WeilConjectures.AlgebraicGeometry.IsAffineOfFiniteClosedCover

/-!
# Affineness of quasi-compact quasi-separated zero-dimensional schemes

Source: Stacks Project, Properties, Tag 0CKV, `lemma-dimension-zero`, final assertion
(blueprint: lem-sfb-qcqs-zero-dimensional-affine).
-/

@[expose] public section

universe u

open CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A quasi-compact quasi-separated scheme whose points are all closed is affine.
The empty scheme is included, with no Noetherian or finite-type hypothesis.
Source: Stacks Project, Properties, Tag 0CKV, `lemma-dimension-zero`, final assertion
(blueprint: lem-sfb-qcqs-zero-dimensional-affine).

Proof:
1. By `lem-pqf-finite-affine-cover-qc-open`, choose a finite affine open cover of `X`.
   Closedness of points restricts to each chart; the empty cover is permitted.
2. Every prime of a chart ring is maximal: `lem-weil-pbc-proper-ideal-contained-in-maximal`
   gives a maximal prime containing it. In `def-weil-affine-spectrum`, a closed singleton
   is `V(S)`, so any prime containing that point belongs to the same singleton.
3. By `lem-weil-pbc-zero-dimensional-spectrum-profinite`, each chart is Hausdorff.
   By `lem-weil-pbc-affine-scheme-qcqs` the charts are quasi-compact, and
   `pqf-lem-qs-intersection-qc` makes their pairwise intersections quasi-compact.
4. An intersection is closed in either Hausdorff chart: separate a point outside it
   from each of its points, choose finitely many neighbourhoods covering the compact
   intersection, and intersect the corresponding neighbourhoods of the outside point.
   Thus the complement of any chart is open on every chart, hence open in `X`.
5. Each affine open inclusion is an immersion by `def-weil-closed-immersion` and has
   closed image by step 4. Apply `lem-weil-pbc-immersion-closed-image-closed-immersion`
   to make it a closed immersion, retaining its original scheme structure.
6. The affine closed subschemes still cover `X`. Apply `lem-sc-closed-affine-union-affine`,
   including its empty-cover case. `IsAffine X` gives `X.isoSpec : X ≅ Spec Γ(X, ⊤)`. -/
theorem isAffine_of_qcqs_of_t1 (X : Scheme.{u}) [CompactSpace X]
    [QuasiSeparated (terminal.from X)] [T1Space X] : IsAffine X := by
  sorry

end AlgebraicGeometry
