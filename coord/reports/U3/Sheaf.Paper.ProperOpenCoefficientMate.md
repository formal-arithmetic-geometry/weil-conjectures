## What changed

Proved `AlgebraicGeometry.Etale.properOpen_coefficient_mate_transposed` in
`Sheaf.Paper.ProperOpenCoefficientMate` without changing its signature. The proof
first proves the untransposed coefficient square, then applies the inverse proper
adjunction Hom equivalence. It works on unbounded objects; the existing lower-bound
hypotheses remain unchanged.

The private proved helpers establish ordinary coefficient/pullback coherence,
localize its entire cube, take scalar and geometric mates, identify the resulting
mate with `finiteCoefficientDirectImageMap` by its universal scalar-unit equation,
and prove the open-extension unit comparison. The final generic calculation
`coefficient_interchange_of_restriction` combines these identities with the
recorded proper/open exchange normalization. Proof imports added:
`Sheaf.CategoryTheory.DerivedExactCube` and
`Sheaf.Paper.EtaleProEtaleScalarMate`. All original public imports remain.

Abstracted the large choice expression in `properOpenCoefficientInterchange`
through the proved normalized existence theorem. The new theorem
`properOpenCoefficientInterchange_eq_recorded` proves that this selects exactly
the original isomorphism. Its restriction/exchange components and inverse open
adjuncts determine the object; no undetermined existence witness is introduced.
This removes repeated elaboration of the large global-family statement and makes
the complete module compile within the unchanged 60-second limit (37.7 seconds in
the checked sandbox set). The only consumer that unfolds this definition is
adapted to use the equality theorem. See
`coord/changes/U3-proper-open-normalized-selection.md` for the definition and
consumer audit. Both existing DAG nodes now record the implemented route.

## Proved and sorry left

Closed one of one original holes:
`AlgebraicGeometry.Etale.properOpen_coefficient_mate_transposed`
(node `lem-sp-proper-open-coefficient-mate-transposed`).

Added zero holes; split off zero unfinished statements. No `sorry` remains in the
item or the adapted consumer. All new private helpers, the normalized existence
theorem, and the equality with the original recorded choice are proved. This is
a proof from existing declared dependencies, including their existing unfinished
theorems, rather than a decomposition into new holes.

## No longer needed

No original imports, declarations, modules, or nodes are withdrawn. The transpose
node no longer needs a direct proof-dependency edge to
`lem-weil-pbc-ringed-topoi-derived-tensor-pullback`: its scalar comparison is supplied
by the already stated `lem-sfb-etale-proetale-scalar-mate`. The ringed tensor result
is still an indirect dependency and is not a globally pruned node. The localized
cube uses `lem-fix-site-open-exchange-localization`, and ordinary coefficient
comparisons use `lem-sbc-canonical-restrict-scalars-functor-comparisons`.

The retained unit route is unchanged. No source-library declarations are changed
or removed.

## Where the brief, the DAG or earlier work was wrong

The mathematical plan was valid, but the claimed reassociation of canonical
comparisons required explicit coherence and exact-localization calculations. The
new proof supplies those calculations instead of leaving them implicit. The
previous global choice definition also made elaboration exceed the per-file
limit. The normalization interface repairs that cost while provably preserving
the chosen map. No statement is disputed or weakened.

## Forced adaptations

`Sheaf.AlgebraicGeometry.EtaleOriginProperOpenInterchange` is unclaimed in the
current claim records. Its original proof fails against the compiled changed
item at original line 237:

```text
error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  (⋯.choose (pullback.fst p i) (pullback.snd p i) p i ⋯).hom.app K.obj
in the target expression
```

Only the rewrite at that line changes (now two lines): replace unfolding
`Etale.properOpenCoefficientInterchange` by rewriting
`Etale.properOpenCoefficientInterchange_eq_recorded`. This returns the expression
to the original recorded choice, so the existing normalization equation applies.
Every declaration signature, visibility, import, and other proof line is retained.

## Second reading by U3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
