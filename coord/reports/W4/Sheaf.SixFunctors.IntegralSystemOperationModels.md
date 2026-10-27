## What changed

Constructed the sequence-ring identification, identity-on-sections ordinary bridge,
universal derived direct image with the published exact inverse factorization,
ordinary exact open extension, and section/representative-normalized Compositors
in IntegralSystemOperationModels. The existential is assembled in Lean from these
constructions and three separate comparison steps. All new helpers in the item
are private and proved; no definition contains sorry or chooses unspecified data
from an unproved mere-existence assertion.

Added proof imports for CoefficientSystemUnboundedComparison (its proved private
derivedImage_exists helper), SemilinearProperOpenMatePasting (its proved private
pushComp_apply helper), MapDerivedCategoryMate, and the three new comparison
modules. Existing public imports and the item's statement are unchanged. No other
existing module or existing node is changed.

Validation: all four Lean modules compiled through lcompile.py. The three new
comparison modules compiled in 51.6, 52.8 and 50.5 seconds, and the final item
compiled cleanly in 28.0 seconds. The original theorem signature and public imports
are retained verbatim; the changed existing node fields are exactly proof,
proof_deps and proof_origin. No cycle passes through any node in this packet.

## Proved and sorry left

Removed the original hole in
WeilConjectures.IntegralSystemRealization.integralSystemOperationModels (1 original
hole; 0 remaining in the item). This is a decomposition, not a complete proof:
three lower holes are added, each in its own module and node:

- integralSystemDirectEvaluation — lem-sf-integral-system-direct-evaluation.
- integralSystemOpenEvaluation_isIso — lem-sf-integral-system-open-evaluation.
- integralSystemOpenComparisons — lem-sf-integral-system-open-comparisons.

Every name above is in WeilConjectures.IntegralSystemRealization. The second
obligation asserts invertibility of one specified mate, rather than choosing an
unrelated evaluation map. The first and third construct proper components of the
original argument, with Operations and Compositors supplied as inputs. None
restates the upper simultaneous existence theorem. The net textual hole change
of this packet is +2; it does not claim a net sorry reduction.

## No longer needed

No original import is removed and no module is withdrawn. The main proof no
longer directly uses lem-pur-coefficient-system-derived-comparison or
lem-coef-semilinear-derived-sections as a package-existence black box. The former
is retained in the direct-evaluation node, and the latter underlies the existing
semilinear K-injective and open constructions and the new comparison nodes; no
global pruning of either module is claimed. The main node instead records the
actual unbounded derived-image helper and the existing semilinear construction
API. No proper/open pasting, tensor-composition, integral realization,
compactification or duality lemma is used to construct the models.

## Where the brief, the DAG or earlier work was wrong

The declared generic comparison theorems use different coefficient-system and
finite-level presentations. They do not directly fill the fixed DirectEvaluation
or OpenComparisons records. SystemOperationExchangeRealization also supplies
systemDirectEvaluation_isIso and systemOpenEvaluationInv_isIso, but for its own
integralComparisonSequencePullback and systemPullEvaluation presentation. Those
statements do not supply the fixed cochain normalization and quotient-transition
fields here without a further identification argument. The construction parts
can nevertheless be proved
using their existing APIs: the ring-map uniqueness and section formulas eliminate
the ordinary bridge and compositor obligations entirely. The remaining splits
are comparison steps, not another version of the full model existence assertion.
No statement is changed or disputed. Empty opens, identity opens, n = 0,
nonflat quotient maps and zero complexes were checked in the proof plans.

## New nodes

lem-sf-integral-system-direct-evaluation: the finite-extension/Yoneda comparison,
with both adjunction equations and the adjacent quotient transition equation.

lem-sf-integral-system-open-evaluation: invertibility of the specified open
adjunction mate, reduced to the exact slice extension formula.

lem-sf-integral-system-open-comparisons: the unit, cartesian slice, tensor slice
and clopen formulas, given already constructed operations and compositors.

All inherit sec-six-functors / sk-thm-sf-compatibility and the original realization
source. No change record is needed: no existing interface or shared definition
is altered.

## Second reading by W4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
