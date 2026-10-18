## What changed

Proved `AlgebraicGeometry.derivedSquareIso_commShift`, with its original signature,
using the existing bounded below localization and factorization APIs. Two proved
private lemmas, registered as local instances, establish compatibility of `mapDerivedCategoryPlusNatIso` and
`mapDerivedCategoryPlusCompIso` with every integer shift. They identify the
comparisons after precomposition with `DerivedCategory.Plus.Qh` as composites of
shift-compatible factorization and homotopy-category comparisons, then use
`NatTrans.CommShift.of_whiskerLeft` and essential surjectivity of `Qh`.
A proved private equality-transport lemma handles equal scheme maps. Expanding
`pullbackSquareComparison_def` then finishes by inversion and composition.

The module compiles without warnings in about 4.3 seconds through `lcompile.py`.
The existing node's proof, proof dependencies and proof origin now describe this
bounded below argument. No statement, definition or public interface changes.
Searches through `msearch.py` (LeanFinder, Loogle, grep) and local source searches
found the existing factorization formulas and homotopy shift instances used here;
no existing theorem directly supplied this square compatibility.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.derivedSquareIso_commShift`
(node `lem-weil-pbc-derived-square-iso-commshift`).

Original holes: 1. Holes closed: 1. Holes added: 0. Split off: 0.
No `sorry` remains in the delivered Lean module. All three private helpers are
proved, and no new public theorem or assumption is introduced.

## No longer needed

Removed the proof imports `Sheaf.AlgebraicGeometry.DerivedCategories` and
`WeilConjectures.AlgebraicGeometry.DerivedCategories`: neither supplies anything
used by this proof. The first is the retired compatibility module; the second's
torsion-cohomology API is unrelated to shift compatibility.

Removed these original proof dependencies from the node:
`def-weil-abstract-derived-category`, `def-weil-pbc-derived-categories`, and
`lem-weil-pbc-triangulated-functor-restriction`.
The argument works directly through the bounded below localization `Qh` and its
already-proved factorization API. It does not perform a separate unbounded
calculation or restrict a newly proved identity. The category dependency remains
in `stmt_deps`, since it still describes the theorem's ambient categories.
No additional module, node or import is made obsolete by the implementation.
The blueprint unit `sk-def-exchange` and its realized declarations are retained.

## Where the brief, the DAG or earlier work was wrong

The original seven-step plan is mathematically valid but longer than necessary
with the current library APIs. The proved factorization formulas on `D+` permit
direct descent of the comparison compatibilities, for all integer shifts at once;
there is no need for a final positive/negative-shift induction.
The existing declaration docstring records that original plan; its statement and
source are preserved, and the updated node records the actual implementation.

The dry run requires a change record for the added section-local commands.
`coord/changes/U2-derived-square-shift-local-helpers.md` records their scope; no
global instance or public declaration is added.

## Second reading by U2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
