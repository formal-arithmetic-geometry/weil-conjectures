/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-!
# Intersections of quasi-compact open subschemes

Source: Weil conjectures blueprint, `sec-nagata-compactification`,
`sk-prop-nagata-sketch-zmt`, lemma `pqf-lem-qs-intersection-qc`
(blueprint: pqf-lem-qs-intersection-qc).
-/

@[expose] public section

universe u

open CategoryTheory.Limits

namespace AlgebraicGeometry

/-- In a quasi-separated scheme, two quasi-compact open subschemes have a quasi-compact
intersection. Source: the Weil conjectures blueprint, lemma `pqf-lem-qs-intersection-qc`
(blueprint: pqf-lem-qs-intersection-qc).

Proof:
1. Express each of `U` and `V` as a finite union of affine opens, using
   `lem-pqf-finite-affine-cover-qc-open`.
2. Distribute intersection over these finite unions. Each intersection of an affine open
   from `U` with one from `V` is quasi-compact by clause (1) of
   `lem-weil-pbc-quasi-separated-affine-cover-criterion`. Finite unions of compact subsets
   are compact, so `U ⊓ V` is quasi-compact. Its openness is built into `X.Opens`.

Equivalently, use `quasiSeparatedSpace_iff_quasiSeparated` and
`QuasiSeparatedSpace.inter_isCompact`, converting compactness between a subset and its
subspace using `isCompact_iff_compactSpace`. -/
theorem compactSpace_inter_of_quasiSeparated (X : Scheme.{u})
    [QuasiSeparated (terminal.from X)] (U V : X.Opens)
    [CompactSpace U.toScheme] [CompactSpace V.toScheme] :
    CompactSpace (U ⊓ V).toScheme := by
  have : QuasiSeparatedSpace X :=
    (quasiSeparatedSpace_iff_quasiSeparated X).mpr inferInstance
  exact isCompact_iff_compactSpace.mp
    (QuasiSeparatedSpace.inter_isCompact (U : Set X) (V : Set X)
      U.isOpen (isCompact_iff_compactSpace.mpr (inferInstance : CompactSpace U.toScheme))
      V.isOpen (isCompact_iff_compactSpace.mpr (inferInstance : CompactSpace V.toScheme)))

end AlgebraicGeometry
