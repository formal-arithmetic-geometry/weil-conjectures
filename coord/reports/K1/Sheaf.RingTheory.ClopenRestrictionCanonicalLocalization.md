## What changed

Filled both theorem proofs in
`lean/Sheaf/RingTheory/ClopenRestrictionCanonicalLocalization.lean`, preserving every existing
signature, definition, import and docstring.

Private proved helpers construct the nonempty filtered neighbourhood index, identify the
idempotent image as a submonoid, and prove that `Localization (denominators g Z)` is a colimit
of the prescribed diagram. The latter uses the localization universal property for its legs
and descents, and uniqueness of algebra maps for compatibility and uniqueness. Transport
along the unique colimit isomorphism gives the localization instance on the chosen colimit.

The spectrum image follows from Mathlib's localization spectrum theorem: disjointness from
the denominators means membership in every clopen neighbourhood. A clopen subset of the open
complement separates any point outside the closed set. The embedding then supplies the
homeomorphism, with its map definitionally equal to contraction. The canonical local-ring
isomorphisms use the recorded upstream `IsLocalization.prime_localRing_residueField_iso`.
Restriction identities and composites use localization uniqueness; contraction and local-map
naturality follow from `AlgHom.comp_algebraMap` and `Localization.localRingHom_comp`.

This implements the existing node's proof plan and keeps the unit route unchanged. Sources
read: the current blueprint's `det-pe-wc-cover-second-stage.proof.md` Preliminaries; Stacks
`proetale.tex`, `lemma-construct`; `algebra.tex`,
`proposition-universal-property-localization`, `lemma-spec-localization`, and
`item-localization-localization`. LeanFinder, Loogle and grep searches were run through
`msearch.py`, and the pinned Mathlib and upstream declarations were read directly.

## Proved and sorry left

Closed both original holes (2 of 2):

- `WContractification.ClopenRestriction.canonical_localization`
- `WContractification.ClopenRestriction.restriction_naturality`

No holes added, no split-off statements, and no `sorry` remains in the delivered module.
All private helpers are proved. The proofs cover empty closed sets, the whole space,
empty spaces, and the zero ring: the top clopen always gives an index object, and the
localization and spectrum results allow a submonoid containing zero.

## No longer needed

None. No imports, modules, nodes, or declared proof dependencies are pruned. The existing
DAG plan matches the proof: idempotent identities, the localization universal property,
the profinite clopen basis, the localization spectrum embedding, and the canonical
local-ring isomorphism are all used. No new proof dependency imports were necessary because
the required APIs were already available through the module's existing imports.

## Where the brief, the DAG or earlier work was wrong

No mathematical or interface defect found. The plan is sufficient without new intermediate
statements: the colimit universal property can be proved directly in commutative algebras,
and the restriction laws follow from the resulting localization uniqueness.

## Second reading by K1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
