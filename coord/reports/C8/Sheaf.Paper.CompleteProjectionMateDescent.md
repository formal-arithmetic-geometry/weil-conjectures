## What changed

`Sheaf.Paper.CompleteProjectionMateDescent.complete_projection_mate_descent`
has a Lean proof of formal descent, invertibility, the prescribed
inverse, and two-variable naturality. The theorem signature is unchanged.
Two proved private helpers establish invertibility of the actual composed
reduction unit on complete objects and naturality of the actual compact-support
projection.

The proper/open reduction square is isolated as
`Sheaf.Paper.CompleteProjectionReductionSquare.projection_reduction_square`.
It is precisely the parent's argument before descent along the completeness units.
It assumes neither completeness nor boundedness nor invertible reconstruction;
its conclusion is only the unreversed comparison square. The main theorem uses
invertible reconstruction to cancel that square and then performs the remaining
argument in Lean. This is a strict decomposition, not a renamed main theorem.

The existing models and maps move verbatim into
`Sheaf.Paper.CompleteProjectionDescentMaps` to avoid an import cycle. The original
module publicly reexports them. No source-library file or target signature changes. The parent statement gets only a
citation to the new definition owner; its mathematical content is unchanged.
The new square is a proof-only import. The extraction is documented in
`coord/changes/c8-complete-projection-descent-maps.md`.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.ProEtale.CompleteProjectionDescent.complete_projection_mate_descent`
(node `lem-sp-complete-projection-mate-descent`). Its module has zero remaining holes.

Added one hole, the public theorem
`AlgebraicGeometry.ProEtale.CompleteProjectionDescent.projection_reduction_square`
(node `lem-sp-complete-projection-reduction-square`). This is the only `sorry`
left in the three delivered Lean modules. The extracted definitions have zero holes.
Thus this delivery is a decomposition: one original hole closed, one strictly
smaller hole added, net zero. The formal unit descent and naturality parts are proved.

The remaining square has its source and complete proof in words in its docstring
and node. On identity compactifications it specializes to tensor/scalar naturality;
on zero inputs both paths are zero. It makes no faithfulness claim about evaluation,
requires the inverse open system projection when that inverse is used, and imposes
no invertibility requirement on the proper exchange or reconstruction maps.

## No longer needed

No module is withdrawn and no parent route is pruned. The original public import
`Sheaf.Paper.ProjectionReductionPresentation` moves to the extracted definition
module and remains publicly available through it. The main module needs only its
shared definitions and the proof-only reduction-square import. The exploratory
`Mathlib.CategoryTheory.Adjunction.FullyFaithful` import was removed; the proof
uses the explicitly supplied unit-isomorphism API instead.

Direct proof dependencies on `lem-coef-sequence-projection-derived-adjunction`,
`lem-coef-sequence-pushforward-limit-projections`, and
`lem-sp-reduction-derived-monoidal-tower` are removed: the specified normalized
adjunction and tensor/pullback models are already supplied in the statement.
The proof directly uses `SpNormalizedEquivalence.unit_isIso` and the unit of the
specified derived-tower equivalence, so it does not need a separate uniqueness-of-
adjunctions or completeness-comparison argument. Accordingly the former direct
proof dependencies `sk-def-pe-derived-completion` and `def-weil-derived-complete`
are no longer proof lemmas; the completeness notion remains in the unchanged
statement and in the normalized-equivalence API.

The generic ringed exchange/tensor coherence, open tensor normalization,
semilinear derived sections, derived monoidal comparisons, and mate-pasting nodes
remain dependencies of the new reduction-square node. Their former top-level
`tool_uses` approvals are removed from the main node because its Lean proof now
uses the square rather than those tools directly. They are not globally pruned.
No unused upstream declaration is removed.

## Where the brief, the DAG or earlier work was wrong

The parent statement/dependency correction is citation-only: it now cites the
new owner of the verbatim relocated maps. Its statement_change lists every DAG
citer; their uses all hold because the theorem signature and definitions are
unchanged. The change record gives the old and new definitions verbatim.

The supplied plan had no declaration with the whole normalized square in the
particular `DescentModels` interface. Its generic coherence and normalization
lemmas use separate presentation interfaces; identifying those presentations and
pasting the proper/open comparisons remains the new square's proof obligation.
Existing existence results for canonical comparison presentations do not directly
prove compatibility for the arbitrary specified normalized model in the theorem.

The final completeness step does not require comparing two unspecified adjunctions:
the definition is explicitly the composite of the supplied normalized adjunction
and the derived-tower equivalence adjunction. `Adjunction.comp_unit_app` gives
its actual unit. The unit-naturality descent and projection naturality are now
formalized without changing any hypothesis.

## New nodes

`def-sp-complete-projection-descent-maps` owns the existing relocated models and
maps. This records their actual definition separately so the new lemma and the
parent can share them. The bodies and signatures are unchanged. The change record
is `coord/changes/c8-complete-projection-descent-maps.md`.

`lem-sp-complete-projection-reduction-square` states only the comparison square
from parent proof steps 2-5, before canceling reconstruction and before using
completeness. Its node carries the generic coherence/normalization proof route,
quotient-representative normalization, and search records. The parent node now
records precisely the square cancellation, actual composite-unit invertibility,
unit descent, inverse formula and two-variable naturality implemented in Lean.

## Second reading by C8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
