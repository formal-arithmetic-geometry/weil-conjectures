## What changed

Restored `Sheaf.AlgebraicGeometry.PicardExternalCoefficientsDirectImages` from its
quarantine archive. Replaced its public import of the empty withdrawn
`Sheaf.AlgebraicGeometry.FieldLinearModuleCohomologyOperations` with the canonical
`WeilConjectures.AlgebraicGeometry.FieldLinearModuleCohomologyOperations`.
This repairs the recorded unknown-identifier error for `externalCupCoefficients` in
its public theorem statement. No declaration signature or proof body changed.
The full restored module compiled cleanly using `lcompile.py` in 9.2 seconds.

Change record: `coord/changes/picard-external-direct-images-upstream-import.md`.

## Proved and sorry left

This is a zero-hole restoration repair. The archived module had zero `sorry`s;
the delivered module has zero `sorry`s. Holes closed: zero. Holes added: zero.
No statements were split off.

The existing complete proofs of
`AlgebraicGeometry.Scheme.Modules.picardExternalCupCoefficients_directImages`
(node `lem-sc-picard-external-coefficients-direct-images`) and the private helper
`isZero_higherDirectImage_of_affine_local` are preserved and compile unchanged.
The proof still uses affine-local cohomology, the ordinary pushforward coproduct,
and the higher-direct-image presheaf comparison as the node specifies.

## No longer needed

Removed the stale public import
`Sheaf.AlgebraicGeometry.FieldLinearModuleCohomologyOperations`, replacing it with
its canonical upstream counterpart. No mathematical node, module or proof dependency
is pruned. The other imports are preserved. No deletion or withdrawal is requested.

## Where the brief, the DAG or earlier work was wrong

The item is a quarantined post-sync import repair, not an unproved theorem.
Its archive already contains a complete proof. The DAG and Lean attachment remain
correct and unchanged. The earlier module imported an empty withdrawn compatibility
path for declarations needed in its public statement.

Repeated search found no shorter applicable theorem: LeanFinder returned generic
Tor and sheaf-cohomology APIs; Loogle did not resolve the queried derived-zero name;
Mathlib grep found the generic right-derived-zero API. The existing proof already
uses the appropriate geometric library declarations. Consumer search covered active
and quarantined Lean sources; the only consumer is the quarantined acyclicity module.

## Second reading by G3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
