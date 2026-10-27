## What changed

Restored `Sheaf.Paper.FiniteTensorReductionData` from its rework quarantine.
In `WeilConjectures.PurityFiniteSetting.FiniteTensorLineComparisonNormalized`,
explicitly set the source and target localization Hom universes of Mathlib's
`Functor.mapDerivedCategorySingleFunctor` to `u + 1`. The fixed scalar adjunction
already uses these universes. Also specify the outer single functor localization
universe and both coefficient-lift universes of `sfFixedRestriction` at `u + 1`.
The single-complex comparison, its inverse,
realization object and adjoint-transpose normalization are retained verbatim
apart from that elaboration annotation. Added a docstring explanation.
The archived `FiniteTensorComparisonEquations` consumer also compiles unchanged
against the restored module (8.5 seconds, no diagnostics).

The existing node keeps every declaration attachment and dependency; its Lean
note records the repair. The change record is
`coord/changes/V8-finite-tensor-reduction-localization-universes.md`.
The current blueprint finite-reduction proof Step 2 and the unit realization
were read; this repair preserves their route.

## Proved and sorry left

This is an assigned definition repair with zero holes in the archived source.
Holes closed: 0. Holes added: 0. Sorries left in the delivered module: 0.
No theorem is split off and no proof is claimed for an imported sorry.
The final module compiled cleanly in 36.8 seconds through `lcompile.py --all`,
with no errors or warnings. The delivery axiom probe also compiled in 17.6 seconds,
checking all 15 declarations with no direct sorry or extra axiom reported
(its only warning is a long line inside the tool-generated probe). The archived version has the build failure recorded
in `coord/rework.tsv`; the repaired version retains all fifteen declarations.

## No longer needed

None. All five public imports, all recorded node dependencies and all archived
consumers remain needed and are retained. No module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The missing live file is a quarantined build failure, not a withdrawn definition.
The original unconstrained single-complex comparison inferred incompatible
localization universes after upstream synchronization. Fixing those universes
repairs the definition without choosing different data or weakening a condition.
`tools/downstream.py --allow-missing` sees zero live consumers; the quarantine
import graph and DAG still show eight consumers, all listed in the change record.
The only textual user of the changed predicate is the signed-reduction existence
statement; its arguments, quantifiers and normalization meaning are unchanged.

Loogle, LeanFinder and Mathlib grep searches all located the existing exact-functor
single-complex comparison in `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`.
No replacement construction or new mathematical result is necessary.

The delivery probe rejected the first annotation-only attempt; inspection of
`sfFixedRestriction` exposed its two independent lift universes. The final
version fixes those as well as the single-functor localization universe.

## Second reading by V8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
