## What changed

Completed the forward implication by computing stalks on finite constant etale charts, proving cardinality loci open on each stratum, and assembling the finite constructible union. Added the proof-only import of the constant-sheaf fibre API and a named converse theorem carrying the remaining Noetherian-induction argument.

## Proved and sorry left

The target theorem `isConstructibleAbelianSheaf_iff_constructible_stalk_cardinality_loci` is proved from the forward argument and the converse theorem. The converse theorem `isConstructibleAbelianSheaf_of_constructible_stalk_cardinality_loci` remains `sorry` and is recorded by node `fin4-lem-stalk-constructibility-criterion-converse`.

## No longer needed

The imported generic irreducible-neighbourhood, reduced-closed-subscheme, filtered-colimit, and stalk-conservativity declarations are not used by the completed forward proof; they remain in the source header because they are the declared route for the split converse. No existing proof-dependency node was removed from the item record.

## Where the brief, the DAG or earlier work was wrong

The blueprint proof is substantially longer than the formal forward direction. The converse requires the full Noetherian induction and is split into one named intermediate theorem rather than leaving an anonymous proof hole.

## New nodes

`fin4-lem-stalk-constructibility-criterion-converse` records the converse direction, its SGA 4 source, and the remaining Noetherian-induction proof.

## Second reading by U6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
