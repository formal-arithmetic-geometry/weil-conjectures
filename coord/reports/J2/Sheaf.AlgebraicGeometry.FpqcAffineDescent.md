## What changed

Proved `AlgebraicGeometry.isAffineHom_of_fpqc_cover` in
`Sheaf.AlgebraicGeometry.FpqcAffineDescent`, with its signature unchanged.
The proof installs the already proved single-morphism affineness descent theorem
`IsAffineHom.descendsAlong_surjective_inf_flat_inf_quasicompact` and applies the
already proved covering-family theorem
`Scheme.of_isPullback_of_ofArrows_mem_fpqcTopology` to the generated fpqc covering
sieve and canonical pullback squares. These are precisely the two declarations
already recorded as this node's `lean_candidates`.

Added proof-only imports of
`WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FlatDescent` and
`WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Fpqc`. Updated the proof docstring
and the node's proof, proof dependencies and proof origin to describe this route.
No statements, definitions, visibility, or public imports changed. No other
modules required adaptation. The unit `sk-thm-p1` does not realize this auxiliary
node as its own statement or a proof step; all of its realized nodes stay intact.

Validation: the revised module compiled through `lcompile.py`, without warnings.
The delivery preflight also compiles its axiom probe. The argument uses no
nonemptiness or finiteness assumption on the original index type, and applies
unchanged to an empty family over an empty base, a singleton family, identity
covers, and different universes for the index and the schemes.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.isAffineHom_of_fpqc_cover`
(node `lem-weil-pbc-fpqc-descend-affine`).

No holes remain in the item. No holes were added or split off. Both source-library
theorems used have complete proofs; this is a proof, not a decomposition.

## No longer needed

Removed proof-only imports:

- `WeilConjectures.AlgebraicGeometry.FpqcDescendQuasiCompact`
  (`lem-weil-pbc-fpqc-descend-quasi-compact`).
- `Sheaf.AlgebraicGeometry.FpqcLocalOnBaseCriterion`
  (`lem-weil-pbc-fpqc-local-on-base-criterion`).
- `WeilConjectures.AlgebraicGeometry.IsSeparatedOfFlatSurjectiveBaseChange`
  (`lem-weil-pbc-fpqc-descend-separated`).

The former eight-step proof is already carried out by the two proved library
declarations, so the following remaining proof-only dependencies do not need
separate imports or proofs for this item:

- `pqf-lem-affine-local-target` (its obsolete `tool_uses` approval was withdrawn).
- `lem-weil-pbc-affine-morphism-permanence`.
- `def-weil-flat-morphism`.
- `def-weil-surjective-morphism`.
- `def-weil-affine-spectrum`.
- `lem-weil-pbc-morphism-affine-schemes-affine`.
- `def-weil-finite-type-morphism`.
- `def-weil-proper-morphism`.
- `lem-weil-pbc-qcqs-over-affine`.
- `lem-weil-pbc-flat-base-change-global-sections-qcqs`.
- `lem-weil-pbc-morphism-into-affine-scheme`.
- `lem-weil-pbc-fibre-product-affine-spectra`.
- `lem-weil-pbc-cartesian-square-pasting`.
- `lem-weil-pbc-flat-morphism-base-change`.
- `lem-weil-pbc-surjective-base-change`.
- `lem-weil-pbc-fpqc-descend-isomorphism`.

The four statement dependencies (`def-pc-scheme`, `def-pc-fibre-product`,
`pqf-def-affine-morphism`, `def-weil-pbc-fpqc-covering`) remain unchanged.
Removing the proof-plan edges does not claim that their underlying Mathlib
notions or the elementary facts used within the source proofs cease to exist.
Only this item's three direct module imports are pruned; other users determine
whether those modules remain in the targets' closure.

## Where the brief, the DAG or earlier work was wrong

The original plan was mathematically valid, but unnecessary to reproduce in Lean:
the node itself already listed the two complete library results that combine to
prove its exact family statement. Neither one alone is the family statement;
combining them, including generation of the covering sieve and the canonical
pullback data, closes the gap. No mathematical statement was corrected.

No new nodes or change records were needed.

## Second reading by J2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
