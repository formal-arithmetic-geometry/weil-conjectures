## What changed

Restored the assigned quarantined module using the archive recorded in
`coord/rework.tsv`. Changed its private `import all` from the upstream
`ProEtaleModule.DerivedCategory` module to the extracted `Sheaf.UpstreamExtra`
module that now contains the constructibility transport and zero helpers.
The archived unit proof and the two finite truncation inductions are unchanged.
All public imports, declarations, types and visibility are preserved.

Change record:
`coord/changes/E1-bounded-constructible-tensor-preservation-rework.md`.

## Proved and sorry left

This is an assigned compile repair with zero original holes, zero holes closed,
zero holes added and zero holes left. Both complete theorem bodies compile:

- `AlgebraicGeometry.ProEtale.CondensedRing.boundedConstructible_tensor_unit`
  (`lem-sfb-dc-tensor-unit`).
- `AlgebraicGeometry.ProEtale.CondensedRing.boundedConstructible_tensor_closure`
  (`lem-sfb-dc-tensor-preserves`).

No statements were split off. A separate consumer importing only this module
applies both theorems with their full archived signatures. The unit construction
uses a rank-zero-to-rank-one presentation in degree zero, and zero presentations
in other degrees; the tensor proof retains the existing degree-zero calculation,
coefficient-specific triangulatedness, and double truncation argument.

## No longer needed

Removed the unused private proof import
`WeilConjectures.ConstructibleSheaf.OpenClosed`. Removed the obsolete
`import all WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory`,
replacing it with the private import of the extracted helpers. The ordinary public
upstream import is preserved. No declarations, modules or DAG nodes are withdrawn,
and no mathematical proof dependency is pruned. The DAG proof route and both Lean
attachments are unchanged.

## Where the brief, the DAG or earlier work was wrong

The synchronization moved the private helpers without updating the archived
`import all`. The rework error is reproducible from the missing private names;
importing their current module restores the original proof. The mathematical
statements and DAG route require no correction. The item has zero holes and is
completed as a compile repair, not as a newly closed proof obligation.

## Second reading by E1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
