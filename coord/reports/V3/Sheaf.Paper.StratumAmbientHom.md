## What changed

The pro-etale theorem in `Sheaf.Paper.StratumAmbientHom` now packages the
componentwise canonical comparison into a natural isomorphism with
`NatIso.ofComponents`.  The comparison and its componentwise isomorphism
property are recorded as the new theorem
`AlgebraicGeometry.ProEtale.stratumAmbientHomComparison` in
`Sheaf.Paper.StratumAmbientProjectionData`, whose proof is the genuinely
separate tensor-Hom/projection calculation.  The parent imports that module
only for its proof.

## Proved and sorry left

The existing étale declaration was already proved.  The pro-etale
`AlgebraicGeometry.ProEtale.nonempty_stratumAmbientHomIso` hole is closed by
real Lean code that uses the new comparison theorem.  The new theorem
`AlgebraicGeometry.ProEtale.stratumAmbientHomComparison` remains one split
hole, with its source and proof plan in its docstring and DAG node
`lem-weil-stratum-ambient-hom-comparison`.

## No longer needed

No proof-dependency imports were removed.  The categorical projection helper
was not needed for the packaging step and is not imported.  The unimplemented
site-specific tensor/projection calculations below the comparison remain the
single split item described above.

## Where the brief, the DAG or earlier work was wrong

The original parent proof plan combines the site-specific tensor/projection
calculation and the final Yoneda packaging in one declaration.  The formal
library already has the latter as a short categorical packaging step, so the
former is split into a separate comparison theorem rather than duplicated in
the parent.

## New nodes

`lem-weil-stratum-ambient-hom-comparison` records the new comparison theorem
and its source.  Its Lean declaration is in
`lean/Sheaf/Paper/StratumAmbientProjectionData.lean`.

## Second reading by V3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
