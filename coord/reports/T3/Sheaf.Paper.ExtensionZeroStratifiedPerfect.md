## What changed

Restored Sheaf.Paper.ExtensionZeroStratifiedPerfect from its assigned quarantine
archive. In the private extendStratification definition, replace the obsolete
LocallyClosedStratification input and output annotations with Scheme.Stratification,
the type now used by IsIntegralStratifiedPerfect. The explicit construction already
provides constructibility, so no mathematical change is needed. Public signatures,
imports, proofs, and the existing DAG attachment and proof route are preserved.
Change record: coord/changes/T3-extension-zero-stratification-sync.md.

Remote single-file compilation via lcompile.py passes without diagnostics in
4.3 seconds. Reviewed the current model predicate, the explicit closed-complement
stratification and vanishing argument, and the open-model transport signature.
Source searches include the quarantined parent, which retains this dependency;
there are no external uses of the theorem name and no forced adaptations.

## Proved and sorry left

This is a zero-hole compilation repair. The archived module contains zero sorry
proofs; the restored module contains zero. Holes closed: none (0 of 0). Holes added:
none. Split off: none. The existing complete proof of
AlgebraicGeometry.Scheme.cbc_extension_zero_stratified_perfect is retained, with
its private helper elaborating against the current upstream structure.
Its node is lem-cbc-extension-zero-stratified-perfect.

## No longer needed

None. No import, declaration, module, DAG dependency, or unit step is pruned.
The quarantined IntegralCompactSupportUniformRestriction parent still cites this
module, so the assigned module and its node attachment are preserved.

## Where the brief, the DAG or earlier work was wrong

The item is an assigned rework repair rather than an open proof hole. The archived
private helper references the removed LocallyClosedStratification interface;
the canonical integral model predicate now quantifies over Scheme.Stratification.
Its existing constructibility fields already match that interface. No statement
or proof-plan correction is required, and no new nodes are introduced.

## Second reading by T3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
