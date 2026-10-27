## What changed

Proved `WeilConjectures.FiniteFieldDatum.geometric_fibre_comparison_hypotheses`
with its original signature in `Sheaf.Paper.GeometricFibreComparisonHypotheses`.
Pullback instances give separatedness and finite type; Mathlib gives the locally
Noetherian and compact-space instances. The existing
`AlgebraicGeometry.exists_topologicalKrullDim_le` supplies the dimension bound.
Characteristic follows from the finite-base cardinality and its injective embedding.
For each stalk, `Units.map` transports `Units.mk0 (l : D.k)` along exactly the
ring map in the statement, including its specified inverse. The existing
`geometricFrobenius` automorphism's two inverse identities give the last clauses.

Added the private proof import `Mathlib.Algebra.CharP.CharAndCard`; retained the
private finite-type/dimension import and all public imports. Updated the node's
proof, proof dependencies, proof origin and obsolete tool approval to match this route.
No definitions, theorem signatures or consumer modules changed.

Validation: the complete module compiles without warnings through `lcompile.py`
(6.7 seconds). The argument handles the empty fibre, arbitrary algebraic closure,
and nonreduced models without additional assumptions. The field nonzero argument
uses both primality and `l != D.p`; no nonzero-stalk assumption is added.

Searches: `msearch.py` LeanFinder found related scheme results, Loogle returned
`CharP.cast_ne_zero_of_ne_of_prime`, and grep/local `rg` found the existing
finite-dimension theorem and characteristic proof patterns. All stated proof
dependencies and the trace unit's realized route were read; no unit step is bypassed.

## Proved and sorry left

Closed 1 hole: `WeilConjectures.FiniteFieldDatum.geometric_fibre_comparison_hypotheses`
(node `lem-fd-geometric-fibre-comparison-hypotheses`).
Remaining holes in the item: zero. Holes added: zero. Split-off theorems: zero.
The dimension result is reused from the existing source-library declaration.

## No longer needed

Removed the private import `Sheaf.SixFunctors.FrobeniusSquareCartesian` and this
proof's dependency/obsolete tool approval `lem-weil-frobenius-square-cartesian`.
Its Cartesian assertions are unnecessary for the inverse identities, which already
belong to the `geometricFrobenius` automorphism from `def-weil-frobenius-detailed`.
This is pruning from this proof, not a withdrawal of that module or its declaration.
All other planned dependencies remain used. No new nodes or modules were introduced.

## Where the brief, the DAG or earlier work was wrong

No statement defect or repair was found. The planned appeal to the full Cartesian
Frobenius square was stronger than required: the existing automorphism contains
both required inverse identities. The explicit Bezout calculation is also unnecessary;
the existing characteristic lemma gives nonvanishing and hence the field unit.
The latest blueprint locates `def-fd-trace-function.md` under `sk-cor-plancherel`,
rather than the older `sk-def-trace` source path; its mathematical setting is unchanged.

## Second reading by M7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
