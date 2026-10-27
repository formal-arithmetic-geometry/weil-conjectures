## What changed

Filled `CategoryTheory.kernelPair_restriction_quasiCompact` in
`Sheaf.CategoryTheory.Sites.KernelPairRestrictionQuasicompact`, preserving its statement.
The private concrete constructions `restrictionHom`, `restrictionInv`, and
`restrictionIso` implement the comparison using pullback lifts. Repeated pullback
extensionality proves inverse identities and naturality, and lift projection
identities prove the six coordinate formulas.

Quasi-compactness follows from two applications of `IsQuasiSeparatedObject`.
Its definition quantifies over arbitrary pullback squares; the second application
uses the square on `K ×_A L` transported by `IsPullback.of_iso_pullback` along the
constructed isomorphism. This avoids a separate invariance-of-quasi-compactness lemma.
Updated the item's node proof and proof dependencies to this categorical argument.
No other existing module or node is changed; the unit route is preserved.
The final file compiled through `lcompile.py` in 9.4 seconds with exit code 0
and no warnings. A source comparison confirms the theorem signature is unchanged.

## Proved and sorry left

Closed the sole original hole, in
`CategoryTheory.kernelPair_restriction_quasiCompact`
(node `lem-trf-kernel-pair-restriction-quasicompact`).
Added zero holes. There are no remaining `sorry` declarations in this delivery,
and no split-off statements. All private constructions have complete bodies and proofs.

## No longer needed

The node `lem-weil-pbc-site-sheaf-sets-limits-sectionwise` is not needed by this
proof: pullback universal properties replace sectionwise computation in a sheaf
presentation. Removed it from this node's `proof_deps` and proof-step `uses`.
Removed the unused proof-only import `Mathlib.CategoryTheory.Sites.Limits`.
It remains available to all its other users; no module is withdrawn.
The statement imports are preserved.

## Where the brief, the DAG or earlier work was wrong

No statement defect was found. The sectionwise limits step is unnecessary:
the explicit coordinate comparison works in any category with finite limits.
The quasi-separatedness predicate already accepts arbitrary pullback squares,
so the final isomorphism transport is included directly in its application.
The Grothendieck-topos hypothesis remains in the unchanged statement, although
the universal-property proof does not use it.

## Second reading by R4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
