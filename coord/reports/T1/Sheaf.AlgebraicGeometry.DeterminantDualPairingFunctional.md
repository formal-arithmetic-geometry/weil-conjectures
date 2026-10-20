## What changed

Completed the retirement assignment recorded in `coord/retire-items.tsv`:
withdraw `Sheaf.AlgebraicGeometry.DeterminantDualPairingFunctional` and attach
`lem-sc-exterior-dual-pairing-functional` to its already-proved upstream twin.

The sole direct consumer, `DeterminantDualAlternatingFamily`, now imports the
upstream module. It precomposes the upstream functional on Over U with the hom
of `exteriorSheafIsoExteriorPower`. The comparison's hom-wedge theorem proves
the required determinant formula. All later alternating-map proof lines and
its statement stay unchanged. Its DAG proof records this transport.

The consumer compiled cleanly through `lcompile.py` (3.6 seconds). A separate
import-only counterfactual failed (8.2 seconds): `q` has values in the dual of
`M.exteriorPower n`, where the unchanged consumer expects the dual of
`M.exteriorSheaf n` (line 56, followed by wedge-argument mismatches). This confirms
that the added transport is necessary. A separate `#print axioms` compile of
the adapted theorem succeeded in 4.7 seconds and reports only `propext`,
`Classical.choice`, and `Quot.sound`; no `sorryAx` is reachable. No source-library file was edited.
The change record is `coord/changes/retire-determinant-dual-pairing-functional.md`.

## Proved and sorry left

The assigned module has zero original holes. Its theorem
`AlgebraicGeometry.exterior_dual_pairing_functional`
(node `lem-sc-exterior-dual-pairing-functional`) is already proved upstream;
this delivery retires the duplicate rather than claiming another hole closed.
The adapted `AlgebraicGeometry.exterior_dual_pairing_local`
(node `lem-sc-exterior-dual-pairing-local`) remains fully proved.

Holes closed: 0 of 0. Holes added: 0. Holes left in delivered Lean: none.
Split-off theorems: none. No axiom or data definition is added.

## No longer needed

The module `Sheaf.AlgebraicGeometry.DeterminantDualPairingFunctional` is withdrawn,
and its sole consumer no longer imports it. Its DAG attachment points to
`WeilConjectures.AlgebraicGeometry.DeterminantDualPairingFunctional`.

The retired copy's proof imports (`Sheaf.AlgebraicGeometry.ExteriorSheafComparison`,
`Mathlib.LinearAlgebra.ExteriorPower.Pairing`, and
`Mathlib.CategoryTheory.Sites.PreservesLocallyBijective`) disappear with the copy.
Their mathematics remains used by the upstream theorem or the consumer.
The functional node no longer needs `lem-sc-exterior-sheaf-comparison` for its own
proof: the unchanged upstream theorem is already in the upstream exterior-power
encoding. The consumer still needs that comparison to preserve its earlier
statement, and its node records it. No other node or upstream declaration is
withdrawn. The unit's route is unchanged.

## Where the brief, the DAG or earlier work was wrong

The generic proving brief suggests a remaining hole, but the exact queue row is
a retirement repair. The current module contains no `sorry` and compiles already.
The significant work is its replacement by the official twin and adaptation of
its consumer across the different exterior-sheaf encodings. Merely changing the
import would select the upstream theorem with the wrong output type; explicit
precomposition and the proved wedge comparison resolve that mismatch.

The C6 extensionality-retirement change record was read and its current
comparison interface is used. No prior proof is replaced by a hole.

## Second reading by T1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
