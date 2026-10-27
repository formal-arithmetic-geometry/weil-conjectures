## What changed

Proved `WeilConjectures.IntegralSystemRealization.integralSystemOpenComparisons`
without changing its statement, the `OpenComparisons` fields, or any shared definition.
The only Lean module changed is the assigned module. Added private, proved helpers
and proof imports for the existing finite native tensor models and the
source-library clopen comparison. Finite full faithfulness and the adjunction mate
API are already provided by the unchanged public Operations import. Updated the
item node's proof, proof dependencies and proof origin to match this route.
Beta and its transpose equation are constructed together in a private subtype;
using its projections avoids unfolding the concrete derived construction when
checking the normalization field. The square is passed as a parameter, with
`c.square` supplied only in the final assembly; this avoids expanding its
transport construction during kernel checking.

Validation: the assigned module compiled cleanly through `lcompile.py` in 9.1 s,
with profiling removed and zero warnings or errors.

The argument first detects the open unit and supported open counits by finite
evaluation. It then constructs base change and projection by the exact inverse
transposes required in the statement. Their invertibility follows from support,
so equality detection by evaluations is unnecessary. For clopen immersions the
existing ordinary comparison and uniqueness of derived right adjoints show that
the direct unit on extended objects is invertible; its composite with direct image
of the inverse open unit supplies the required comparison.

The two existing biduality-unit nodes
`lem-coef-derived-system-evaluation-calculus` and
`lem-coef-native-open-tensor-models-existence` are used as tools. The former is
already the calculus selected in `IntegralSystemOperations`; its joint
conservativity and fixed tensor evaluation fields are needed here. The latter
supplies finite native models for exactly those chosen tensor functors. The
compatibility unit's generic open normalization result does not itself identify
these finite chosen models. No biduality conclusion is used, and traversing both
nodes' statement/proof dependency closures finds no path back to this item.
The finite open exchange and realization comparison are existing transport tools;
the source-library clopen isomorphism is reused unchanged.

## Proved and sorry left

Closed the one original hole:
`WeilConjectures.IntegralSystemRealization.integralSystemOpenComparisons`
(node `lem-sf-integral-system-open-comparisons`).
No `sorry` remains in the item; zero holes were added and zero statements split off.
This is a proof from existing declared dependencies, including the existing theorem
`WeilConjectures.CoefSupportOpenTensor.nativeOpenTensorModels_exists`; its proof
obligation is unchanged by this delivery. No arbitrary object is defined from an
unproved existence statement: the native model witness is used only inside a proof
to establish finite essential-image membership.

## No longer needed

The item's proof no longer needs `lem-sf-semilinear-proper-open-mate-pasting`
(`Sheaf.SixFunctors.SemilinearProperOpenMatePasting`): no semilinear pasting or
comparison of a separately chosen square map with `c.square` is used. The required
map is defined by the specified transpose, and support proves its invertibility.
This removes that dependency from this node, without withdrawing its module or
claiming it has no other consumers.

The item does not directly invoke the normalized tensor-model existence result
`lem-sf-open-tensor-normalization`. The finite native models supply the tensor
support assertion for exactly the recorded calculi. The general normalization
module remains needed transitively, including through the unchanged public
`IntegralSystemOperations` import, so it is not globally pruned. No original
import was removed. The finite open FullyFaithful module and the adjunction mate
API are supplied transitively, so no extra direct imports are needed for them.
No module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The original plan required identifying a separately constructed geometric square
with the fixed compositor square. That calculation is unnecessary: its prescribed
transpose already defines the comparison, and its factors are isomorphisms once
the target is known to have open support. Joint conservativity is used only for
invertibility; it does not assert that finite evaluations detect equality.

The same argument reduces projection to support rather than transporting its
whole normalized transformation. Existing finite native tensor models provide
that support, avoiding another split of this obligation. The statement and unit
route are preserved. Empty opens, identity immersions, clopen empty complements,
and zero complexes introduce no extra hypotheses in these categorical arguments.

## Second reading by Y5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
