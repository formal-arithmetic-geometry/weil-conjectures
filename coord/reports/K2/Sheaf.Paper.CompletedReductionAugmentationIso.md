## What changed

Proved `WeilConjectures.CompletedCoefficientPushforward.reductionAugmentation_isIso`
in `Sheaf.Paper.CompletedReductionAugmentationIso`. All existing signatures, definitions,
public imports and docstrings are preserved. Added only private proof imports and proved
private helpers.

The proof first extracts local derived completeness from the given Roos-triangle witness,
using the existing Roos/intrinsic equivalence's proved auxiliary results. The existing
principal-cone criterion and its normalized quotient comparison then make the explicit
quotient Roos unit invertible. A canonical limit-cone isomorphism and uniqueness of total
right derived functors compare this model with the supplied `source.limit`. The section
formula for `a` and naturality of the zero-homotopy lift identify the whole specified map,
including its zero second coordinate. The proof does not replace that map by an arbitrary
triangle isomorphism.

Updated the item's DAG proof and direct proof dependencies to describe this argument.
No consumer adaptation or definition change is needed. The unit route is preserved.
The added, scoped helper variables are documented in
`coord/changes/K2-completed-reduction-augmentation-proof-context.md`, as requested
by stage-3 preflight. All 993 transitive consumers retain the same interface.

Validation: the complete module compiled through `lcompile.py` in 27.9 seconds,
with no errors or warnings. The original theorem signature was checked unchanged.

## Proved and sorry left

Closed 1 of 1 original holes:
`WeilConjectures.CompletedCoefficientPushforward.reductionAugmentation_isIso`
(node `lem-pur-completed-reduction-augmentation-iso`). Added 0 holes. There are no
`sorry`s in the delivered module or any other delivered Lean file. No new statements
are split off.

The proof uses the existing
`WeilConjectures.IntegralPrincipalCone.localCriterion`
(node `lem-pur-integral-principal-cone-local-criterion`), whose existing admission is
unchanged. Thus this delivery proves the assigned theorem from the project's stated
proof dependencies; it does not claim that their transitive proofs are all finished.

## No longer needed

No original Lean import was removed. No whole module is withdrawn.
The planned direct dependencies `lem-weil-l-adic-extension-integers-dvr`,
`lem-weil-pbc-ringed-strict-tower-homotopy-limit` and
`lem-weil-proetale-countable-products-exact` are not separately invoked here.
The normalized principal-cone/quotient results already supply the regular quotient
comparison. The strict Roos derivation supplies the normalized total derived functor;
no separate ringed-tower homotopy-limit theorem is needed. Exact products are supplied
by `det-pe-products-exact`. These removals concern this node's direct proof dependencies,
not the still-used transitive dependencies of other declarations.

## Where the brief, the DAG or earlier work was wrong

No false statement or definition was found. The stated Roos/intrinsic equivalence
has an auxiliary adic datum whose construction is unnecessary for the implication
used here. Its existing proved auxiliary lemmas and the same principal-cone criterion
supply that implication directly, preserving the independent universes. The given
flat-term hypothesis and the auxiliary prime remain verbatim in the public theorem
although this proof only needs K-flatness.

## Second reading by K2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
