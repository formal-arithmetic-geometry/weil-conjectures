## What changed

Restored the quarantined item as a public compatibility import of
`WeilConjectures.AlgebraicGeometry.Picard.CanonicalSinglePullbackComparison`.
The source already supplies the three original declaration names and the
complete invertibility proof. Redirected the existing node
`lem-pc-canonical-single-pullback-comparison` to that source implementation;
its statement, proof plan, dependencies, and unit route are unchanged.

The concrete repair replaces the invalid duplicate implementation/import chain
with the adopted source construction. The repaired module exports the canonical
map, its additive structure, and its invertibility theorem to its existing
quarantined importers. It is retained for them, rather than withdrawn. No source
library declaration is edited or removed, and no consumer adaptation is needed.

Change record:
`coord/changes/F3-canonical-single-pullback-source-interface.md`.

Validation: the repaired import compiled through lcompile.py in 1.4 seconds.
A separate source check compiled in 6.1 seconds: it checked the exact map type,
proved by rfl that its definition is precisely the pinned counit composite, and
applied `isIso_canonicalSinglePullbackMap` with the original hypotheses.
The same checks also compiled through the restored Sheaf compatibility import
together with the flat-module proof dependency (1.5 and 6.1 seconds), confirming
that the restored public export works without duplicate declarations. The
axiom reports of all three declarations contain only `propext`,
`Classical.choice`, and `Quot.sound`. Searches checked both live and quarantined
consumers and the DAG parents; the change record lists 26 consumer modules.

## Proved and sorry left

This is a zero-hole quarantine/interface repair. The archived item has zero
sorries, and the restored module has zero sorries. Holes closed: none (0 of 0).
Holes added: none. Split off: none. Sorries left in the delivery: none.

`AlgebraicGeometry.Scheme.Modules.isIso_canonicalSinglePullbackMap`, attached
to `lem-pc-canonical-single-pullback-comparison`, remains fully proved in the
adopted source. Its proof constructs the tensor comparison, applies
`isIso_modulePullbackComparison_of_isFlatOver_identity` using intrinsic flatness
of invertible modules, and composes with the mapped adjunction-uniqueness
isomorphism. This delivery claims interface repair, not a new mathematical proof.
The additive structure and map construction have no proof holes either.

## No longer needed

Removed the archived direct public import of
`Sheaf.AlgebraicGeometry.DerivedPullbackComposition` (now a retired empty module).
The adopted source exports
`WeilConjectures.AlgebraicGeometry.DerivedPullbackComposition` instead.
The archived direct public `LocallyFree` import and private
`FlatModuleCanonicalDerivedPullback` import are handled by the source
implementation with their original public/private visibility.

No mathematical node, source declaration, or proof dependency is pruned. In
particular retain the flat-module comparison, module pullback adjunction,
derived pullback composition, and this node itself. The 29 DAG parent nodes
(including parents whose Lean is quarantined) retain their dependencies. The
unit's realized arrays are empty and its route is unchanged. The compatibility
module is required by its archived direct importers and is restored.

## Where the brief, the DAG or earlier work was wrong

The item is an assigned rework restoration, not a current Lean file with an
open proof. Its source is preserved in the quarantine path in coord/rework.tsv;
that archive already has a complete proof and zero holes. The recorded failure
is a duplicate derivedPullback environment after the upstream sync. The node's
Lean attachment still names the quarantined Sheaf implementation, although the
source now implements the same three declarations. It now points to that
existing source implementation.

The duplicate inventory labels the source map definition as changed. Reading
the two bodies shows the construction is still the same pinned counit
composite: the source explicitly qualifies `AlgebraicGeometry.derivedPullback`
to avoid resolving the newer `Scheme.Modules.derivedPullback`. The compiled rfl
check verifies the intended formula; no arbitrary isomorphism or existence
witness is substituted. Restoring both sets of declarations would recreate the
name collision, so this repair publicly imports the source implementation.

The live downstream.py command reports the quarantined item as an unknown
module. Therefore consumer checks also searched quarantine/ and the mathematical
DAG; absence from live Lean was not treated as permission to withdraw the node.
Quarantined consumers still need their independent restoration assignments;
this delivery does not claim to repair their unrelated imports or proofs.

## Second reading by F3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
