## What changed

Replaced the proof hole of
`WeilConjectures.sfQcqsCompactSupport_normalizedLift_existsUnique` by an explicit
natural transformation and a complete adjunction calculation. The transformation
is the reduction/total-limit unit, followed by the total limit of a strict
proper/open coefficient-system map, followed by the inverse recorded realization.
The private generic lemma `projection_transpose` proves the projection equation
from the two normalized units, naturality of the total-limit projection, and the
recorded target projection equation. Cancellation of each finite reduction
isomorphism and natural-transformation rigidity prove uniqueness.

Added two lower theorem modules and matching nodes. The strict comparison supplies
a map on **all ambient inputs**, before total inverse limit, and independently
identifies the native total limit with the already recorded integral action. The
rigidity theorem isolates the uniqueness part for natural transformations between
these two functors. Neither lower theorem asserts the item's unique existence.
All existing statements, definitions, public imports, and source-library files
are unchanged. Only the item's proof and private imports changed.

Validation: both new modules compiled individually through `lcompile.py`
(41.8 s for rigidity, 40.3 s for the strict comparison). The corrected item
compiled against their sandbox artifacts in 4.0 s, with no diagnostics.
Both existing declaration types were also checked verbatim against the source;
all delivered Lean lines are at most 100 characters.

## Proved and sorry left

This is a decomposition, not a completed mathematical proof of the full obligation.
The item originally had one textual hole. Its body now has zero holes:
`WeilConjectures.sfQcqsCompactSupport_normalizedLift_existsUnique` is proved from
the two lower statements. The private `projection_transpose` is proved in full.

Two holes are added, each the entire proof of a named public theorem:

- `WeilConjectures.qcqsCompactSupport_strictReductionComparison`, node
  `lem-qcqs-compact-support-strict-reduction-comparison`.
- `WeilConjectures.sfQcqsCompactSupport_reduction_ext`, node
  `lem-qcqs-compact-support-reduction-rigidity`.

Thus one upper hole is replaced by two lower holes; the net textual count is -1
holes closed. No arbitrary witness is used to define data: the native functor and
its evaluation are local explicit composites, and the two existential witnesses are
eliminated only inside the theorem proof.

## No longer needed

No existing public import is removed and no existing module or node is withdrawn.
The new strict-comparison module imports `CompactSupportNativeSystemEvaluation`;
it does not need the later `CompactSupportNativeSystemTransition` import.
The parent's direct proof dependencies are now the two lower nodes. Its former
five dependencies remain in their proof plans:
`lem-weil-compact-support-reduction-tower-functor`,
`lem-weil-compact-support-representative-independence`,
`lem-sf-integral-open-reduction-comparison`,
`prop-weil-pbc-direct-image-limits`, and
`lem-weil-pbc-ringed-strict-tower-homotopy-limit`.
There is no claim that these modules are globally pruned.

The downstream `CompactificationStrictRealization` and
`CompactificationCompletedRealization` cannot supply a proof here: their import
closures already contain this item. The similar native-system aliases in
`CompactSupportScalarLimitReduction` and `CoefSupportOpenTensorModel` are likewise
downstream; the import-direction tool rejects both routes. The theorem therefore binds its native composite and evaluation locally from
the existing lower factors; it adds no duplicate public definitions.

## Where the brief, the DAG or earlier work was wrong

The parent's one prose step contains both a strict-system geometric construction
and a separate rigidity assertion. The existing representative-independence
statement supplies its recorded projection-normalized realization, but does not
state either a comparison from the ambient completed proper/open functor or
rigidity of arbitrary natural comparisons with equal reductions. These are now
explicit obligations rather than hidden in the final assembly.

`integral_reductions_jointly_faithful` is not a direct replacement: it requires a
`FiniteFieldDatum`, `SixFunctorOperationDatum`, and `SixFunctorSpace`. This item's
base field is arbitrary and its structure morphisms need not be separated.
The new rigidity obligation retains the original natural-transformation scope;
it makes no assertion that arbitrary derived-limit projections are jointly monic.

The current blueprint proof cited in the parent describes the ordered proper/open
scalar comparison, rather than a ready-made Lean theorem with this normalization.
The paper's Definition 6.7.6 and Lemma 6.7.7 (printed p. 56) define the
separately derived proper/open composite and assert its constructibility and
compactification independence; Remark 6.7.8 explicitly warns against deriving
the abelian composite instead. The new native system retains the separate open
and proper factors. The normalization and rigidity details are the agent-written
steps inherited from the parent's plan, not verbatim assertions of that lemma.
No target, unit statement, or unit route was changed.

## New nodes

`lem-qcqs-compact-support-strict-reduction-comparison`, module
`Sheaf.Paper.QcqsCompactSupportStrictReductionComparison`: a strict native sequence
comparison on every ambient input, its evaluation formula, and the independent
projection-normalized identification of the recorded integral functor with that
native sequence's total limit. Source: the parent's construction step,
Bhatt--Scholze 6.7.6--6.7.7 and Stacks 0941/0F7J. Zero input, empty schemes, and
level zero (coefficient exponent one) are included.

`lem-qcqs-compact-support-reduction-rigidity`, module
`Sheaf.Paper.QcqsCompactSupportReductionRigidity`: equality of natural
transformations between the specified functors follows from equality of all their
finite scalar reductions. This is the parent's uniqueness step, with no existence
assertion. Its proof obligation is distinct from objectwise faithfulness.

Both nodes record LeanSearch, LeanFinder, Loogle and local source searches. The
Mathlib hits are the generic adjunction unit/naturality and ordinary limit lemmas;
none states these geometric comparisons. No existing shared interface changed,
so there is no consumer adaptation or change record.

## Second reading by M4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
