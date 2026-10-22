## What changed

Retire Sheaf.AlgebraicGeometry.QcqsStrictLocalRestrictionIsomorphism, the zero-hole
retirement assigned in coord/retire-items.tsv. Its node now points at the adopted
WeilConjectures theorem with the verbatim upstream signature. The sole direct
consumer, Sheaf.AlgebraicGeometry.QcqsStrictLocalModuleComparison (unclaimed), proves
invertibility inside its existing comparison construction. It imports the general
ModuleSectionsIsoTransport theorem privately and uses the official set comparison,
the canonical small/full ring-colimit isomorphism and pullback symmetry. The source
and target bijections preserve the representative equations, so cancellation proves
invertibility. No new public or private theorem duplicates the withdrawn declaration.

All public signatures, public imports and all definition bodies of the consumer are
unchanged. No source-library file or target statement changes. Update the consumer
node to record the direct proof and remove its dependency on the retired theorem.
Change record: coord/changes/S2-qcqs-strict-local-isomorphism-retirement.md.

Validation: the original item compiled in 6.0 seconds. The adapted consumer compiled
in 9.7 seconds with no warnings. The delivery gate checks compilation and axioms.
The import/use scan found one direct consumer and no other use of the removed name.

## Proved and sorry left

The assigned retirement starts with 0 holes. Holes closed: none (0 of 0).
Holes added: none. Holes left in the delivered Lean files: none. No statements split off.
AlgebraicGeometry.Etale.exists_qcqsStrictLocalModuleComparison remains completely
proved with its original signature, now including its own invertibility argument.
The adopted AlgebraicGeometry.Etale.isIso_qcqsStrictLocalRestriction_of_formula
remains unchanged and proved in WeilConjectures.

## No longer needed

Withdraw lean/Sheaf/AlgebraicGeometry/QcqsStrictLocalRestrictionIsomorphism.lean.
Remove its private import from QcqsStrictLocalModuleComparison. The consumer's proof
no longer uses lem-weil-pbc-strict-local-module-restriction-isomorphism; the node stays
attached to the adopted theorem for other uses. The old item node's transport and set
comparison dependencies now belong directly to the consumer node; the adopted
isomorphism node uses lem-weil-pbc-strict-local-module-restriction-bijective instead.
ModuleSectionsIsoTransport, SmallStrictLocalSectionMaps, geometric-stalk machinery and
the official set comparison all remain needed. No other module or node is pruned.
The unit sk-thm-iff statement and proof route are unchanged.

## Where the brief, the DAG or earlier work was wrong

The generic proof brief describes an item containing sorry, but the queue and
retire-items.tsv identify this one as retirement: the live source already has zero
holes. A bare import swap to the adopted twin would fail because its target uses the
full strict-local model. The consumer therefore retains its exact small-model target
and proves the required property using canonical transport. No mathematical statement
is disputed, weakened or replaced by an assumption.

## Second reading by S2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
