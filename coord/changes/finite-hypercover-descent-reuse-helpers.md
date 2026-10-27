# Reuse the extracted finite-hypercover descent helpers

## Reason

Returned delivery 806135950c2 duplicated the private theorem statements already
preserved by the scheduled upstream sync in
`Sheaf.UpstreamExtra.WeilConjectures.AlgebraicGeometry.FiniteHypercoverDescentParts`.
The duplicate-statement landing check correctly refused it. Lean's `import all`
already supports reusing those private helpers, as its existing section-colimit
consumer does. Reuse them instead of copying them into the upstream item.

## Old and new

The upstream item retains exactly its current public import, docstrings, theorem
signatures and declaration attributes. Its three sorry bodies are replaced by
the recovered proofs from preferred upstream version 438e3d04508. A private proof
import of all declarations of the extracted helper module supplies the existing
helpers; no new helper statements, public declarations or definitions are added.

The extracted helper module drops only the public import of the upstream item.
Its 39 private helper declarations, signatures, visibility, bodies, other imports
and options stay verbatim. None uses the three upstream theorems. Removing that
unused import is necessary to reverse the dependency without an import cycle.

The sole existing direct consumer,
`Sheaf.AlgebraicGeometry.GrothendieckHypercoverSectionColimit`, adds a direct
public import of the upstream item. This preserves the declarations previously
reexported through the helper module for all of this consumer's downstream
importers. Its declarations and proofs stay verbatim.

## Consumers and holders

- Upstream item: held by T3; proof restoration only.
- Extracted helper module: unclaimed when checked on 2026-10-24; import repair
  only. The new consumer is the upstream item itself.
- Section-colimit module: unclaimed when checked on 2026-10-24; the only existing
  direct importer of the helper module, as reported by tools/downstream.py
  --direct. The added import preserves its previous public import closure.

No theorem statement, definition or target meaning changes. No DAG proof route
changes; the helpers implement the existing proof steps. The independent reader
should check that the helper file differs by exactly one removed import and that
the consumer differs by exactly one added import.

## Status

All three modules compiled without errors or warnings through lcompile.py:
helper module 28.7 seconds, upstream item 18.3 seconds, consumer 6.9 seconds.
Source checks confirm that the upstream theorem statements and public imports
are identical. Pending delivery preflight and independent maintainer review. The maintainer should
register the upstream item's private proof import of the extracted helper module
in coord/upstream-statement-exceptions.tsv so the next sync retains the proofs.
