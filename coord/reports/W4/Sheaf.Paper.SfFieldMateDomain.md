## What changed

Replaced the hole in `WeilConjectures.sf_fieldMateDomain` by the assembly of its five
exchange fields. Geometry comes from `sf_baseChange_geometry_hypotheses`. The smooth
finite-field and common-stage fields apply the recorded coefficient theorems after
transposing the square; the conditional constructible representative is the image
of the given stage isomorphism under the inclusion, with `StageSystem.ι_map_eq` at
every larger field. The proper common-stage field uses `qbar_properBaseChange`.

For the proper rational field, proved that the coefficient prime annihilates the
first lifted quotient. The original-datum preservation theorem supplies endpoint
membership. The new comparison lemma transports both membership and invertibility
from the specified datum exchange to the `sbc` complete-subcategory mate. Fullness
and rationalization finish the field. No existing statement, definition or public
signature was changed.

Locally bound expensive limit and scalar-extension implementations, selected the
existing derived-module instances, and disabled unused structure-code generators,
as in the neighboring coefficient modules. These are elaboration controls only.

Added `Sheaf.Paper.SbcDatumExchangeComparison` for the remaining normalized exchange
comparison. This is one geometric-condition-free step of the argument: it asserts
an equation between the existing integral maps, without asserting constructibility,
proper base change, smooth base change or any rational/common-stage conclusion.

## Proved and sorry left

Closed: `WeilConjectures.sf_fieldMateDomain` (node
`lem-sf-bc-field-mate-domain`), from the existing stated results and the comparison
below. Original hole count: 1. Item holes remaining: 0.

Added and remaining: `WeilConjectures.sbcDatumExchangeComparison`, node
`lem-sf-sbc-datum-exchange-comparison`, in its own new module, with the complete
unit-normalization proof in words in its docstring. Added hole count: 1.
This delivery is a decomposition, with net holes closed minus added equal to zero;
it does not claim an unconditional sorry-free target proof.

## No longer needed

Removed private proof imports `Sheaf.Paper.FourArrows`,
`Sheaf.Paper.CompletedBaseChangeMap`, `Sheaf.Paper.CommonStageCalculus`,
`Sheaf.Paper.ConstructibleCompleteBaseChange`,
`Sheaf.Paper.AmbientCompleteCoefficientCategories`,
`Sheaf.Paper.PbcScalarExtension`, and `Sheaf.Paper.PbcDescentFunctors`.
The complete-proetale theorem is imported directly.

The direct finite-extension theorem `thm-weil-pbc-finite-extension` is not used:
its coefficient ring is at a different universe, whereas the preservation and
complete-proetale APIs accept the existing lifted `pbcIntegralDatum` directly.
The rationalization argument itself is written here.

The proof no longer directly invokes `cor-weil-pbc-constructible-complete`,
`def-weil-pbc-four-arrows`, `def-weil-pbc-completed-base-change-map`,
`prop-weil-pbc-scalar-extension`, or `prop-weil-pbc-descent-functors` to assemble
these fields. Their constructions and facts remain transitive prerequisites of
the coefficient theorems and are not withdrawn. `def-exchange-projection` and
`def-sbc-ambient-complete-coefficient-categories` remain statement prerequisites;
the assembly needs no separate proof invocation of them. The new comparison node
retains the specified completed-map identification instead of treating isomorphic
endpoints as an equality of exchanges. No Lean modules are withdrawn.

## Where the brief, the DAG or earlier work was wrong

The planned finite-extension application does not directly fit: that theorem uses
an unlifted coefficient field in `Type (u + 1)`, while this item's actual field is
in `Type u` and its integer ring is lifted. The existing original-datum preservation
and complete-proetale declarations avoid changing either coefficient construction.

The plan also glossed over the comparison between the `sbc` complete-subcategory
mate and the datum strict-tower exchange. `sbcCompletedExchange_strictLimit`
compares to its own strict realization, and `pbcActualCompletedExchange_transport`
starts from the actual ambient reflector mate. Neither states the precise `sbc`
comparison needed here. The new node isolates exactly that missing glue.

Mathlib searches used LeanFinder for proper/smooth rational base change,
LeanSearch for completion-unit comparison, Loogle for `mateEquiv` and `map_isIso`,
and grep for the concrete exchange names. The hits give generic derived adjunction,
mate and functor APIs; none states this concrete comparison. Local search checked
both library roots and the current blueprint. Edge cases: the comparison uses no
properness or smoothness and makes no finite-evaluation detection claim; its
reflector cancellation applies to zero inputs and empty schemes. The proper proof
uses a positive prime annihilator. The stage formula includes the identity extension.

The original-datum preservation, completion-unit and reflector APIs from other units
are generic tools for the coefficient transport already prescribed by this unit;
no step of the unit route is bypassed. Existing source-library declarations are untouched.

## New nodes

`lem-sf-sbc-datum-exchange-comparison`:
`dag/nodes/sec-six-functors/lem-sf-sbc-datum-exchange-comparison.json`, realized by
`WeilConjectures.sbcDatumExchangeComparison` in
`lean/Sheaf/Paper/SbcDatumExchangeComparison.lean`. It compares the specified
complete-subcategory integral mate with the ordered datum exchange using canonical
source/target isomorphisms and the completion-unit equation. Its proof dependencies
record the existing normalized completed operations, strict transport, compositor,
reflector mate factorization, datum unit equation and completion reflection.
No change record is needed because there is no signature or definition change.

## Second reading by W4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
