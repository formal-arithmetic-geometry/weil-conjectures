## What changed

Restored `lean/Sheaf/AlgebraicGeometry/StandardSingleFlatCounitLocalizationPair.lean`
from the exact quarantine archive named in `coord/rework.tsv`. Added the explicit
public import `WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyModel`,
whose proved instance `ModuleCat.baseDerivedTensor_extendScalars_additive` is
needed to elaborate the public theorem's homotopy scalar-extension functor.
Every other byte, including the theorem signature, docstring and proof, equals
the archive. No source-library module is modified.

The unmodified archive fails with missing scalar-extension additivity instances
in its statement and its resolution-theorem application. The repaired item
compiles without errors or warnings through `lcompile.py` (4.2 seconds).
A separate `#print axioms` check reports exactly `propext`, `Classical.choice`,
and `Quot.sound` (4.1 seconds). The import-direction check allows the provider.

The consumer inventory includes both live sources and quarantine archives:
zero live users, one direct archived consumer and 93 transitive archived
consumers. The unchanged direct consumer independently lacks the same public
instance provider in its own statement. In a scratch copy, adding that provider
lets its original theorem statement and entire proof compile against the
restored item (27.4 seconds). This confirms that the existing call to this
item requires no adaptation. The consumer and scratch checks are not delivered;
its separate rework assignment is preserved. No consumer signature changes.

The existing node `lem-pc-standard-single-flat-counit-localization-pair` retains
its Lean attachment and its proof dependency
`lem-pc-base-derived-extension-resolution`. Its existing route already applies
the general scalar-extension existence theorem and retains its universal pair;
that is exactly the archived proof. No node update or new result is necessary.
The unit route is unchanged. The Stacks derived scalar-extension construction
was read in `more-algebra.tex`, `lemma-derived-base-change` (Tag 06Y6).

Searches: LeanFinder returned additive/exact functor and derived-category
infrastructure, but no more direct unbounded existence theorem; Loogle reported
unknown identifier for `Functor.IsLeftDerivedFunctor`. Local ripgrep found the
existing complete resolution theorem and the existing additivity instance.

Change record:
`coord/changes/B4-standard-single-flat-counit-localization-pair-additivity.md`.

## Proved and sorry left

This assigned rework repair has zero original holes and zero remaining holes.
`AlgebraicGeometry.standardSingleFlatCounit_localization_pair` is restored with
its complete existing proof and only the three permitted axioms. Holes closed:
none (0 of 0); holes added: none; split-off statements: none; every `sorry` left
in this packet: none. This is an import and restoration repair, not a newly
closed theorem hole or a decomposition.

## No longer needed

No import, mathematical node, module, unit step or proof obligation is pruned.
Both original imports remain necessary: the presentation module supplies the
statement predicate and the resolution module supplies the proof. The one added
public import provides the statement's additivity instance. The quarantine
archive and all existing dependency attachments are preserved.

## Where the brief, the DAG or earlier work was wrong

The generic proof brief describes an item with holes, but this quarantined
rework item already had zero holes. Restoring the archive alone does not compile
against the current published interfaces: the scalar-extension additivity
instance must be imported explicitly. The prior B3 consumer check reported that
this archive compiled against its then-current sandbox; the present published
build instead produces the missing-instance errors recorded here. The existing
DAG statement and proof route remain correct.

## Second reading by B4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
