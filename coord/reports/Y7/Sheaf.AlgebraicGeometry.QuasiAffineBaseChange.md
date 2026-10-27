## What changed

Proved `AlgebraicGeometry.isQuasiAffineHom_baseChange` in
`Sheaf.AlgebraicGeometry.QuasiAffineBaseChange`, preserving its full signature.
Over each affine open, the inverse image is quasi-affine, hence compact and
separated. The Mathlib affine-local criteria therefore give `QuasiCompact f`
and `QuasiSeparated f`. Apply the already proved source-library theorem
`IsQuasiAffineHom.of_isPullback` to the defining pullback square.

Removed the two unused private proof imports, rewrote the proof docstring,
and updated the item's proof, proof dependencies and proof origin to this route.
Removed the obsolete `lem-weil-pbc-relative-spec-base-change` tool approval.
The source library, public imports, all definitions and signatures are unchanged.

The source theorem and Mathlib criteria were read in full. LeanFinder, Loogle,
and the launcher grep search ran; direct source searches found the exact source
result and the two missing affine-local derivations. A server compilation passed
without diagnostics. The delivery preflight independently checks axioms.

## Proved and sorry left

Closed the sole hole:
`AlgebraicGeometry.isQuasiAffineHom_baseChange`
(node `lem-trf-quasi-affine-base-change`).
Proved 1 of 1 sorries; zero holes left in this module, zero added and zero split off.
This is a complete proof, not a decomposition into unproved intermediate results.

## No longer needed

Removed private imports:
- `Sheaf.AlgebraicGeometry.RelativeSpecBaseChange`
- `Sheaf.AlgebraicGeometry.QuasiAffineRelativeSpecEmbedding`

The item's direct proof no longer needs these former dependency nodes:
- `lem-trf-quasi-affine-relative-spec-embedding`
- `lem-weil-pbc-relative-spec-base-change`
- `lem-weil-pbc-open-immersion-base-change`
- `lem-weil-pbc-qcqs-morphism-permanence`

The latter two Mathlib stability facts are already encapsulated in the proved
source-library base-change theorem. No claim is made that these nodes or modules
are unused by the rest of the library. No module or declaration is withdrawn.
The fibre-product dependency remains. The canonical quasi-affine embedding node
now records the absolute compactness and separatedness facts used directly.

## Where the brief, the DAG or earlier work was wrong

The original split and statement review correctly observed that the source-library
base-change theorem has explicit quasi-compactness and quasi-separatedness
hypotheses, but did not exploit that these follow immediately from the definition
of quasi-affine morphism by the existing Mathlib affine-local criteria.
Consequently the relative-spectrum route is unnecessary for this item.
No mathematical statement was changed. The unit `sk-i-curve-zero` has no realized
statement or proof step assigned to these auxiliary relative-Spec nodes; the
shorter proof preserves the unit and its route. No compactness assumption on the
whole base, nonemptiness, or finite-presentation condition enters the argument;
the affine-local criteria apply equally to empty schemes.

## Second reading by Y7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
