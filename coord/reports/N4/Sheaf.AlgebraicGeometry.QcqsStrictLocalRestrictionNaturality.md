## What changed

Retired Sheaf.AlgebraicGeometry.QcqsStrictLocalRestrictionNaturality in favor of
WeilConjectures.AlgebraicGeometry.QcqsStrictLocalRestrictionNaturality, per the
retire-items assignment. Updated its DAG attachment. Adapted its sole direct
consumer, Sheaf.AlgebraicGeometry.QcqsStrictLocalModuleComparison, to import the
official base-change cone directly. The consumer now proves its
small-presentation cocone equation directly from the two cone projection formulas,
pullback extensionality, adjunction naturality, and functoriality. Its definitions
and all public signatures remain unchanged. Updated the parent node's proof route.

Change record: coord/changes/N4-strict-local-restriction-naturality-retirement.md.

## Proved and sorry left

The item had zero sorries; zero holes closed and zero holes added. No sorry remains
in the retired module or adapted consumer. The local refinement-compatibility proof
in exists_qcqsStrictLocalModuleComparison is complete. The official source theorem
qcqsStrictLocalRestriction_naturality is retained unchanged, with its complete proof.

## No longer needed

Withdrawn: Sheaf.AlgebraicGeometry.QcqsStrictLocalRestrictionNaturality. Removed its
only import and call from QcqsStrictLocalModuleComparison. The official naturality
module need not be imported by the consumer either. The naturality node stays
attached to the official theorem; the parent comparison no longer depends on that
node, because it checks the transported small-model graphs directly. No mathematical
unit or adopted-source declaration is removed. No new modules or nodes are added.

## Where the brief, the DAG or earlier work was wrong

The generic proving brief describes a holed item, but this assignment is the zero-hole
retirement listed in coord/retire-items.tsv. The official theorem uses
strictLocalizationToBase, whereas the recently adapted consumer uses
strictHenselizationStructuralMap and smallStrictHenselizationBaseChangeMap. They
cannot be substituted definitionally. Keeping the consumer's definitions and proving
its concrete compatibility avoids changing downstream meanings.

The first consumer-only compile encountered stale published dependencies importing
the already retired SetsPushforwardStalkStrictHenselization copy. Compiling the current
unchanged transport, bijectivity and isomorphism modules with the consumer resolves
that old-environment collision; they require no source edits.

Validation: the adapted consumer and all six unchanged direct importers compiled
without warnings, each within the single-file limit. The three unchanged support
modules were compiled in the same import-ordered set.

## Second reading by N4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
