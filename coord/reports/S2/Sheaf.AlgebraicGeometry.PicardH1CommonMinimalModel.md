## What changed

Restored `Sheaf.AlgebraicGeometry.PicardH1CommonMinimalModel` from its quarantine
path and repaired the post-sync universe elaboration in the private restriction
helper. The `overMap`, `overFunctor`, and `overFunctorMap` calls now specify
universe `v`, allowing the derived-category comparison to elaborate. The public
theorem statement, declarations, imports, and DAG statement are unchanged.

The module compiles with `lcompile.py` and contains no `sorry`, forbidden
declarations, or new axioms. The three split lemmas used by the proof are the
existing modules `DescendedInvertibleNeighbourhood`, `PicardDirectImageFibreBetti`,
and `ResidueRankModelDifferential` already present in the shared library.

## Proved and sorry left

The archived module already had zero holes. The existing complete proof of
`AlgebraicGeometry.Scheme.picard_h1_common_minimal_model` now elaborates against
the current library. Holes closed: 0 of 0; holes added: 0; holes remaining: 0.
This delivery repairs a compilation failure rather than claiming a new proof.

## No longer needed

No imports, nodes, or modules were pruned. The proof uses all proof-only imports
present in the restored module; its public imports remain unchanged.

## Where the brief, the DAG or earlier work was wrong

The quarantined proof was valid before the source-library sync but relied on
implicit universe inference for `overMap` and `overFunctor`. The synced derived
category declarations require the universe to be fixed explicitly. This is a
proof elaboration repair only; no mathematical statement or route was changed.

## New nodes

None.

## Second reading by S2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
