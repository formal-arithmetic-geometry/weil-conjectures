## What changed

Replaced the hole in `finiteDualizing_reduction_coherent` by an explicit pasting
argument. Postcomposition with restriction of `wL.reduction n` turns the goal into
an equality between finite dualizing maps. Target coherence cancels the upper
target reduction; the finite mixed quotient square, source coherence, naturality
of the mixed scalar map, and the scalar quotient transition square finish it.
The existing statement and public import are preserved.

Added `CoefScalarReductionExchange`, which constructs the mixed scalar/quotient
map as the inverse mate of the canonical restriction square. Its single-quotient
coefficient square is proved on representatives, and its normalized restriction
identification uses `finiteDualizingRestriction_eq`. The mixed map is deliberately
a natural transformation with no invertibility assertion: quotient coefficient
extension need not be flat.

Added two independent transition obligations. One concerns arbitrary complete
complexes and the tensor quotient comparison; it has no dualizing datum. The
other concerns only finite dualizing terms and their counits; it has no integral
object or chosen presentation. These are strictly different parts of the original
argument, and the main theorem uses both source and target coherence to combine
them. There is no integral lift or finite-evaluation faithfulness assumption.

## Proved and sorry left

Original hole closed, conditional on the two new obligations:
`WeilConjectures.IntegralFiniteExtension.finiteDualizing_reduction_coherent`
(node `lem-sf-integral-finite-dualizing-coherence`). The item has zero remaining
holes, originally one. This is a decomposition, not a net proof: one upper hole
is replaced by two lower holes.

New proved helper theorems are
`WeilConjectures.IntegralFiniteExtension.scalarQuotient_square` and
`WeilConjectures.IntegralFiniteExtension.scalarQuotient_restrict`.

Holes added, and every hole in the delivered files:

- `WeilConjectures.IntegralFiniteExtension.quotient_reduction_transition`
  (`lem-sf-integral-scalar-quotient-transition`), in
  `Sheaf.SixFunctors.CoefIntegralScalarQuotientTransition`.
- `WeilConjectures.IntegralFiniteExtension.finiteU_quotient_transition`
  (`lem-sf-finite-dualizing-mixed-quotient`), in
  `Sheaf.SixFunctors.CoefFiniteDualizingMixedQuotient`.

Each is a public named theorem with proof exactly `by sorry`, its source and a
complete proof in words, and its own DAG node. Neither restates the original
claim: one is independent of all exceptional data, and the other is entirely
finite-level. Identity extensions, equal levels, exponent one, and the empty
scheme obey the same formulas. No definition contains a hole.

All four modules passed remote compilation in the last full run: the constructed
exchange module in 40.5 seconds, finite counit square in 39.6 seconds, scalar
transition in 50.0 seconds, and the completed main proof in 52.8 seconds.
Profiling showed the scalar statement itself elaborated in 87.3 milliseconds;
local irreducibility prevents expansion of its large comparison definitions.
Temporary profiling options were removed before delivery.

## No longer needed

No existing import was removed and no module is withdrawn. The original public
models import remains necessary for the statement. The item now privately
imports the two transition lemmas; it does not directly use the former planned
proof dependencies `lem-weil-finite-free-completed-scalar-comparison`,
`lem-pur-compact-support-integral-coefficient-comparison`,
`lem-coef-finite-free-extension`, or `lem-coef-finite-dualizing`. They remain
available through the models or belong to the proofs of the new obligations;
none is claimed globally pruned. No unit statement or step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The plan's tensor reassociation and finite-counit transposition are not exposed
as mixed extension/restriction equations by the existing declarations. The
same-field cocycle in `finiteDualizingCoefficientComparisons` does not directly
state the cross-field square, and invertibility of the completed scalar
comparison does not by itself give the normalized transition equation. The new
lemmas record these two missing interfaces explicitly.

Searches used LeanFinder (eight unrelated adic-completion/coalgebra hits), Loogle
(`Adjunction.homEquiv_naturality_right`), LeanSearch (general mate calculus), and
Mathlib/project `rg` (no duplicate mixed transition theorem). The construction
uses Mathlib `mateEquiv`, not a new choice of a mixed comparison. The unit record
`sk-prop-sf-biduality-general` has no realized statement or step here; its route
and the existing coherent dualizing presentations remain intact.

## New nodes

`def-sf-scalar-reduction-exchange`: single quotient, coefficient square, normalized
restriction identification, canonical restriction square, and its scalar mate;
module `Sheaf.SixFunctors.CoefScalarReductionExchange`. All data are constructed,
and both helper theorems are proved.

`lem-sf-integral-scalar-quotient-transition`: the tensor quotient comparison
respects normalized reduction transitions for an arbitrary complete complex;
module `Sheaf.SixFunctors.CoefIntegralScalarQuotientTransition`.

`lem-sf-finite-dualizing-mixed-quotient`: the finite cross-field counit comparison
respects exceptional quotient transitions; module
`Sheaf.SixFunctors.CoefFiniteDualizingMixedQuotient`.

The original node's proof, proof dependencies, and proof origin are updated to
match the explicit pasting argument. No definition or statement of an existing
declaration is changed, so no change record or consumer adaptation is needed.
All newly introduced dependency paths were checked: none creates a cycle back
to a delivered node; all cited nodes exist.

## Second reading by M3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
