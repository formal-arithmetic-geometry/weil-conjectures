## What changed

Filled `AlgebraicGeometry.ProEtale.sfToProEtBaseChange_naturality` in
`Sheaf.AlgebraicGeometry.SfFiniteExceptionalInverseImage`. Extensionality reduces the
site morphisms to their underlying maps; simplification removes identity composites,
and reflexivity identifies the two induced pullback maps. The statement, definitions,
imports, and docstrings are unchanged. The whole module compiled without diagnostics
through lcompile.py in 11.4 seconds.

The shorter-route search found the same elementary calculation in
`AlgebraicGeometry.ProEtale.toProEtCompOverPullbackIso`, in the source module
`WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStar`. Its proof is
`by ext; simp; rfl`; the delivered proof spells these steps out directly, requiring
no additional import or dependency. The proof works for arbitrary scheme morphisms,
including identity morphisms and empty schemes, as the original statement requires.

Searches run through msearch.py: LeanFinder for naturality of inclusion of etale
schemes into proetale schemes and base change (eight general scheme/pullback hits,
no exact match); Loogle for `"pullback", "map"` (generic pullback-map declarations);
grep for `toProEt.*pullback|pullback.*toProEt` (zero Mathlib hits). Repository rg found
the source-library site-square construction above. The blueprint definition and its
unit were read; this proof only completes its auxiliary site-square naturality.

## Proved and sorry left

Closed one of one original holes:
`AlgebraicGeometry.ProEtale.sfToProEtBaseChange_naturality`.
Zero holes remain in the item; zero holes were added; zero statements were split off.

## No longer needed

None. No imports, nodes, or modules were removed. All five existing public imports
continue to support the module's definitions. No additional theory is needed for
this elementary naturality equation, and no proof-dependency imports were added.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was needed. The docstring already describes the direct
proof. No node has this module as its primary `lean.module` attachment; its docstrings
refer to `def-weil-exceptional-inverse-image`, whose current attachment is the broader
coefficient-system construction. That node has no proof steps or proof dependencies
to change for this auxiliary proof. No DAG changes are delivered.

## Second reading by R2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
