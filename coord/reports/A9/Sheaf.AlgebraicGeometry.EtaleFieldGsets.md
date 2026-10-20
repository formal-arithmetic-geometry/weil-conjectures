## What changed

Retired `Sheaf.AlgebraicGeometry.EtaleFieldGsets` in favor of
`WeilConjectures.AlgebraicGeometry.EtaleFieldGsets`, as assigned by the
2026-10-20 retirement hand-off. All 14 direct consumers import the official twin
and register its existing `AlgebraicGeometry.etaleFieldDiscreteForget₂` and
`AlgebraicGeometry.etaleFieldActionForget₂` as instances. Their bodies are
identical to the copy's former instances. This preserves the consumer definitions,
theorems, proofs, and transitive instance interface. One documentation reference
now uses the upstream instance name. No upstream file or target statement changes.

The node `lem-exc-etale-field-gsets` now points at the upstream module, file and
existing `AlgebraicGeometry.etaleFieldGsets` declaration. Only its `lean` field
changes; the mathematical statement and proof plan stay intact. The copy is
absent from sandbox `lean/` and listed in `deleted.txt`.

The complete packet passed `deliver3.py --no-push` on 2026-10-20 (dry-run commit
`2ad6c2783f5`): all 14 adapted consumers and two unchanged compilation
intermediaries compile, the axiom probes pass, and server preflight accepts the
packet for CODEX review. The unchanged intermediaries are
`DiscreteContinuousRepToCommGrpFull` and `DiscreteContinuousRepToCommGrpEssSurj`;
they refresh compiled imports and introduce no source changes. Import-closure
checks find no remaining consumer reference to the retired copy and no new pair
of conflicting Sheaf/upstream twins.

Change record: `coord/changes/A9-retire-etale-field-gsets.md`.

## Proved and sorry left

Original item holes: 0. Holes closed: none. Holes added: none. Holes remaining in
the item: none, because it is withdrawn. No split-off statements. No consumer
proof is replaced by `sorry`. All 16 compiled packet sources contain zero
`sorry` tokens. This is retirement of a duplicate, with its complete proof
reused upstream.

## No longer needed

Pruned module: `Sheaf.AlgebraicGeometry.EtaleFieldGsets`. All 14 direct public
imports are replaced by the official twin. The copy's duplicate theorem and
instance names `AlgebraicGeometry.hasForget₂TypeTopCat` and
`AlgebraicGeometry.hasForget₂DiscreteContActionType` are no longer needed.
The instances are supplied by the existing upstream declarations. No
mathematical dependency node or upstream proof is pruned; the unit route stays
intact.

## Where the brief, the DAG or earlier work was wrong

The earlier re-export wrapper did not satisfy full retirement. Registering the
upstream instances in consumers permits removal of that wrapper. The DAG's Lean
attachment still pointed at the copy and now points at its official twin.

Earlier attempts were refused by a delivery counterfactual that still supplied
the deleted module from the baseline. The launcher tool now accounts for
`deleted.txt`; this resumption passed that check and the complete preflight.
No launcher script, claim, budget, approval metadata or compiler artifact was
modified to bypass a check.

## Forced adaptations

The retirement brief explicitly authorizes all direct consumer migrations. Two
are currently held by other groups:

- `Sheaf.CategoryTheory.DiscreteContActionFiniteOrbitCoproduct` (Y3): line 8
  imports the upstream twin; lines 22–23 register its existing instances. With
  only the import switched, the original lines 48–50 and 52 fail with
  "failed to synthesize instance of type class HasForget₂ (Type w) TopCat".
- `Sheaf.CategoryTheory.DiscreteContinuousRepToCommGrp` (K9): line 9 imports
  the upstream twin; lines 20–21 register its existing instances. With only
  the import switched, elaboration fails with the same missing `HasForget₂`
  instance, followed by cascading errors.

The original files import the explicitly withdrawn module and cannot remain
unchanged in this retirement. All existing signatures, visibility, proofs and
definition bodies are retained. The global instance registrations preserve
instance synthesis for public importers as well. The change record lists the
full downstream closure and holders. The maintainer's independent reader
reviews the migration and the necessary API adjustments.

## Forced adaptations

### Sheaf.CategoryTheory.DiscreteContActionFiniteOrbitCoproduct
Original imports module(s) explicitly withdrawn in deleted.txt: Sheaf.AlgebraicGeometry.EtaleFieldGsets. Those imports must be migrated in this delivery; the baseline's compiled copies are not valid counterfactual dependencies. Adapted module compiled in the delivered set. CODEX verifies the migration and every accompanying API adaptation is needed.

### Sheaf.CategoryTheory.DiscreteContinuousRepToCommGrp
Original imports module(s) explicitly withdrawn in deleted.txt: Sheaf.AlgebraicGeometry.EtaleFieldGsets. Those imports must be migrated in this delivery; the baseline's compiled copies are not valid counterfactual dependencies. Adapted module compiled in the delivered set. CODEX verifies the migration and every accompanying API adaptation is needed.

## Second reading by A9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
