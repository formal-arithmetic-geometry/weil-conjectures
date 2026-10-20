## What changed

Repaired the zero-hole item
`Sheaf.AlgebraicGeometry.StrictHenselizationLocalPresentation` by providing the
small-colimit presentation still needed by its live divisor-quotient consumer.
The proved compatibility theorem has the distinct name
`AlgebraicGeometry.Scheme.smallStrictHenselizationRing_local_presentation`.
It uses the existing upstream `strictHenselizationRing_local_presentation` and the
canonical `smallStrictHenselizationColimitIso`. A proved private helper checks the
structural-map equation on a representative colimit leg. The inverse ring comparison
transports the local-base algebra structure and the universal pointed-etale cocone.

The sole source edit to
`Sheaf.AlgebraicGeometry.Morphisms.StrictHenselDivisorQuotientPresentation`
is its application of the new compatibility name. Its signature, docstring,
imports, visibility and remaining proof are unchanged. That module is unclaimed.
The item's old small-colimit theorem is renamed while keeping its hypotheses and
conclusion exactly. Its direct chart/triples proof is replaced by the shorter
transport from upstream. Its public structural-map import changes to the upstream
module to avoid duplicate declarations when importing the retained theorem.
No source-library file is changed.

The existing node `lem-sbc-geometric-strict-henselization-local-presentation`
now attaches to the small-colimit compatibility theorem. Its natural-language
statement and dependency lists are unchanged. Its proof records both the retained
upstream argument and the additional canonical transport. All parent edges and the
unit route remain intact. There is no duplicate mathematical node.

Change record:
`coord/changes/B4-small-strict-henselization-local-presentation.md`.

## Proved and sorry left

Original item holes: 0. Holes closed: 0. Holes added: 0. Holes remaining: 0.
This is an interface repair, not a hole closure or a decomposition.

Proved:
`AlgebraicGeometry.Scheme.smallStrictHenselizationRing_local_presentation`
(node `lem-sbc-geometric-strict-henselization-local-presentation`), together with
its private `comparison_base` helper. The existing
`AlgebraicGeometry.Scheme.strictHenselizationRing_divisor_quotient_presentation`
proof remains complete after its application is adapted.
No declaration in the delivered Lean files contains sorry; no split-offs.

Validation: both delivery modules compile together without warnings (3.7 and 0.0
seconds in a remote check). The immediate regularity caller compiles unchanged in
1.9 seconds, and the other direct importer CoordinateMaximalBranchStratum compiles
unchanged in 2.1 seconds against the sandbox artifacts. Independent `#print axioms`
checks of the new presentation and the divisor-quotient theorem list exactly
`propext`, `Classical.choice`, and `Quot.sound`.

Edge cases: a field base is included; no nonunit, divisor, regularity, reducedness,
or Noetherian hypothesis is introduced. Nilpotents are preserved by the ring
isomorphism. A geometric point over the zero ring cannot exist. The chosen
localization action is explicitly pulled back through the canonical isomorphism;
no data is taken from a holed existence theorem.

## No longer needed

Removed private proof imports from the item:
`WeilConjectures.AlgebraicGeometry.EtaleLocalRingTriples` and
`WeilConjectures.RingTheory.EtaleResidueTriplesLocalizedStrictHenselization`.
The retained upstream presentation still uses both, so no mathematical node or
module is pruned. All four existing proof dependencies remain needed.
The old public `Sheaf.AlgebraicGeometry.StrictHenselizationStructuralMap` import is
replaced by `WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap`.
Keeping it produces a duplicate `strictHenselizationStructuralMap_eq` import error
from the Sheaf module and upstream StructuralMapExtension. Both direct importers
compile after the replacement. The old item's duplicate public theorem name is
removed; its small-colimit statement is retained under the new compatibility name.

Searches before proof: LeanFinder for the geometric-to-local-algebra presentation
returned henselian and localization results, without an exact match; Loogle for
`CommRingCat.isoToRingEquiv` reported an unknown identifier; msearch grep for
`IsStrictHenselization|smallStrictHenselizationColimitIso` found no Mathlib match.
Local source search located the already proved upstream presentation and the
comparison calculation in CompatibleStrictHenselizationCoreData. Those existing
constructions give the shorter transport proof used here.

## Where the brief, the DAG or earlier work was wrong

At session start the dispatched item was a withdrawn, declaration-free module.
Its retirement record described the small-colimit consumer as quarantined and
absent, but that consumer is live and applies the old theorem at line 65. During
the dry run the shared delivery base refreshed, restoring K1's complete direct
proof and original small-colimit Lean attachment. The packet and change record
have been reconciled with that restored base. Original and delivery holes are
both zero; this delivery replaces that direct proof with reuse of the existing
upstream theorem and resolves the two implementations' shared public name.

The upstream theorem's Lean statement uses the other colimit and structural map.
Its direct application does not preserve the small-colimit consumer's type.
The canonical comparison supplies the missing compatibility. With the delivered
item interface, the original consumer fails with
`Unknown identifier strictHenselizationRing_local_presentation`; changing the one
application repairs it. The existing DAG node suffices for this exact small-colimit
statement. Its four proof dependencies and the unit route are preserved. No new
node or statement weakening is needed.

The first required delivery dry run passed compilation and preflight at
`445ac5db366` (CODEX); the report and change record were then corrected for the
refreshed base, and the dry run is repeated before pushing.

## Second reading by B4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
