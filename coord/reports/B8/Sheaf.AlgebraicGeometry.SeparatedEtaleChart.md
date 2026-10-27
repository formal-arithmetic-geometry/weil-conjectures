## What changed

Proved `AlgebraicGeometry.AlgebraicSpace.separated_etale_chart` with its signature unchanged.
Added two private proof imports: `Mathlib.CategoryTheory.Limits.Yoneda` and
`Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers`.

For each scheme test of the chart diagonal, construct the equalizer of its two
maps to U in Sch/S. Yoneda preserves this equalizer, giving the required presheaf
pullback square. Mathlib's `isClosedImmersion_equalizer_ι_left` proves that its
projection is a closed immersion because U is separated.

For the second clause, take the representing square supplied by the etale
hypothesis. Its scheme W maps monomorphically into C ×_S U, as proved using the
pullback's hom-ext property and Yoneda faithfulness. A scheme monomorphism is
separated; the projection C ×_S U -> C is separated by base change. Their
composite is the desired projection.

Updated the item's DAG proof, proof dependencies and proof origin to this route.
No public interface or definition changed. The single-file server compile passed
without errors or warnings in 6.9 seconds. The delivery tool performs the final
compile and declaration axiom audit.

## Proved and sorry left

Closed one hole: `AlgebraicGeometry.AlgebraicSpace.separated_etale_chart`
(node `lem-a1-separated-etale-chart`).

Holes added: none. Holes remaining in the delivered module: zero.
No split-off theorems. The proof uses Mathlib and the existing algebraic-space
definitions; it does not depend on any unfinished theorem of AlgebraicSpace.

## No longer needed

No imports removed, no nodes or modules withdrawn, and no existing proof
dependency pruned. The separate construction of a scheme representing U ×_E U
and the second cartesian diagonal square in the old plan are unnecessary: direct
equalizers handle diagonal tests, and the monomorphism into C ×_S U handles the
second clause. All five existing dependency nodes still supply the notions and
scheme permanence facts used by the new argument.

## Where the brief, the DAG or earlier work was wrong

No statement error found. No hypothesis or conclusion was changed. The proof
works for empty test schemes and empty U as well: the equalizer and universal
properties require no points. The argument does not assume E, S or C separated.
Only representability of the etale map is needed in the second clause.

The node's source field still cites Morphisms Tag 01UA, whereas its proof and
Lean docstring correctly use Tag 01QR for closed-immersion base change. This
pre-existing metadata issue was already recorded in the stage-1 review; the
source field is outside this delivery's permitted node edits.

## Second reading by B8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
