## What changed

Proved `WeilConjectures.IntegralLineReduction.integral_line_chain_evaluations`
without changing its statement or either existing definition. The proof compares the
sectionwise sheaf tensor with the canonical monoidal tensor, constructs ordinary
cancellation using the prescribed evaluations, and proves its triangle from the
existing line inverse-pair calculation. Zero uses the coefficient-unit constraints;
negative exponents use the symmetry of that inverse-pair equivalence.

The ordinary comparison and cancellation, including the integer cases of the
triangle, are constructed over an arbitrary ringed site before specializing to
the coefficient sheaf. A private generalization of the signed powers and reversed
evaluation specializes definitionally to the existing constructions. The unit
triangle uses abstract monoidal coherence. These interfaces share the pairing
construction and avoid repeatedly checking the concrete localization data.
The unit/counit transport calculation is proved for arbitrary additive functors.
The ordinary cancellation is lifted degreewise and transported through the existing
`BifunctorSingle` collapse. The proof computes both generator formulas and identifies
the transported unit and counit, so their triangle follows from the transported
equivalence. All added helpers are private. Explicit site-smallness and
sheafification instances, and the existing cochain monoidal instance, are registered
locally for proof elaboration. Added only proof imports of the line inverse-pair module,
`BifunctorSingle`, and the signed-line equivalence module. Updated the node's proof,
proof dependencies, and proof origin to match.

## Proved and sorry left

Closed the one original hole:
`WeilConjectures.IntegralLineReduction.integral_line_chain_evaluations`
(node `lem-pur-integral-line-chain-evaluations`). Added zero holes. No `sorry` remains
in this delivery, and no intermediate obligation is split off.

## No longer needed

The proof does not require `lem-pur-flat-single-derived-normalization` or an import
of `Sheaf.Algebra.Homology.FlatSingleDerivedNormalization`: the already implemented
single-summand chain collapse works without flatness or derived localization.
Removed that proof dependency from the node. There were no baseline proof imports
to remove, no module is withdrawn, and no claim is made that the normalization
module is unused by other parts of the project. The other declared dependencies
remain in the proof route.

## Where the brief, the DAG or earlier work was wrong

The planned argument is valid. Its reference to the full flat-single derived
normalization theorem is unnecessary for this chain-only statement. Its underlying
`BifunctorSingle` construction suffices and supplies the generator calculation
without introducing another proof obligation. No statement, definition, target,
unit route, or consumer interface was changed.

## Second reading by M8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
