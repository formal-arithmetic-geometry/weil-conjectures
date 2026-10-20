## What changed

Retired `Sheaf.CategoryTheory.ExtExactFunctorIdentityComparison`, which duplicated
an already proved upstream theorem under the name
`CategoryTheory.Abelian.Ext.exactFunctorIdentityComparisonSheaf`.
The canonical result is `CategoryTheory.Abelian.Ext.exactFunctorIdentityComparison`
in `WeilConjectures.CategoryTheory.ExtExactFunctorIdentityComparison`.
Its signature is identical after removing the Sheaf suffix from the name.

Redirected the existing node's Lean attachment to that upstream theorem, preserving
its statement, proof steps, dependencies, source, unit route, and audit fields.
Adapted the single remaining caller, ScalarAbelianExtFactorization, by changing
the import at original line 10 and the theorem name at original line 160.
Also wrapped the existing local-instance signature at original line 30,
without changing any tokens: deliver3.py refuses its pre-existing long-line warning.
All source-library files are unchanged. Change record: `coord/changes/retire-ext-identity-comparison-A2.md`.

Validation: lcompile.py compiled the adapted consumer in 31.8 seconds,
and the final wrapped file without warnings in 32.1 seconds. A separate
scratch profiler run with the compiled overlay passed in 36.2 seconds;
no profiling options are present in the delivery. The
retirement test first compiled an empty item module, then confirmed the
original consumer error recorded below. The adapted consumer compiles with
all existing signatures and definitions intact.

## Proved and sorry left

The item starts with zero sorry holes. Closed: 0; added: 0; split off: 0; remaining: 0.
The removed theorem exactFunctorIdentityComparisonSheaf and its private helper were
already fully proved. Their existing canonical upstream counterparts are retained.
No declaration with a sorry is added or left in the adapted consumer or
the withdrawn item.

## No longer needed

Withdrawn module: `Sheaf.CategoryTheory.ExtExactFunctorIdentityComparison`.
Removed its only remaining import, in
`Sheaf.AlgebraicGeometry.ScalarAbelianExtFactorization`, replacing it with the
canonical upstream import. Removed the duplicate declaration
exactFunctorIdentityComparisonSheaf and the unused private helper in that Sheaf
module. The upstream helper is preserved for its existing upstream consumer.

No DAG node is deleted or pruned. The node
lem-weil-pbc-ext-exact-functor-identity-comparison now refers to the canonical
upstream declaration; its Mathlib dependencies def-pc-ext and
lem-weil-pbc-exact-functor-derived-factorization remain needed by that proof.
The Mathlib Ext.Map import remains provided by the upstream module.

## Where the brief, the DAG or earlier work was wrong

The assigned item has no sorry. The remaining defect is duplication: its DAG Lean
attachment points to the Sheaf copy although its upstream audit already records
the canonical proved theorem. The historical upstream review suggests
mapExactFunctor_eq_of_iso plus mapExactFunctor_id, but the former API is absent
from the pinned Mathlib and source extension; the source extension's latter lemma
requires EnoughInjectives. The existing canonical identity comparison already has
the required general HasExt signature and avoids that extra hypothesis.

Current msearch.py Loogle and LeanFinder queries returned generic exact-functor Ext
APIs; online Loogle also returns newer Mathlib results absent from the pinned source.
Local searches and direct signature comparison found the exact upstream result.
The older twins census lists two additional Sheaf callers that are now absent;
tools/downstream.py and current whole-root searches find only the caller adapted here.

## Forced adaptations

`Sheaf.AlgebraicGeometry.ScalarAbelianExtFactorization` is held by V2.
The original file compiled against the withdrawn item's empty module fails at
line 160, column 16:

```text
error(lean.unknownIdentifier): Unknown constant `CategoryTheory.Abelian.Ext.exactFunctorIdentityComparisonSheaf`
```

The dependency-forced edits are original line 10 (proof import: Sheaf to
WeilConjectures) and original line 160 (the canonical theorem name).
The original signatures, visibility,
definition bodies, instances, and all other proof lines remain identical.
The first dry run then refused the compiling packet solely because of the
pre-existing line-30 length warning (COMPILES WITH WARNINGS, nothing pushed).
To meet the required 100-character limit and zero-warning delivery gate,
the same local-instance signature is wrapped onto two lines. This changes
only whitespace and is required by that gate; it is not a mathematical adaptation.

## Forced adaptations

### Sheaf.AlgebraicGeometry.ScalarAbelianExtFactorization
Original against changed dependencies failed:
```
/tmp/forced-adaptation-to3c3_mn/lean/Sheaf/AlgebraicGeometry/ScalarAbelianExtFactorization.lean:30:100: warning: This line exceeds the 100 character limit, please shorten it!

Note: This linter can be disabled with `set_option linter.style.longLine false`
/tmp/forced-adaptation-to3c3_mn/lean/Sheaf/AlgebraicGeometry/ScalarAbelianExtFactorization.lean:160:16: error(lean.unknownIdentifier): Unknown constant `CategoryTheory.Abelian.Ext.exactFunctorIdentityComparisonSheaf`

(with the modules compiled into /tmp/forced-adaptation-to3c3_mn/.lbuild) [39.6 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.

## Second reading by A2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
