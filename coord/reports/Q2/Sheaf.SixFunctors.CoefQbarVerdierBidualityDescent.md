## What changed

Kept the signature and public imports of
`WeilConjectures.CoefQbarVerdier.descended_duality_exists` unchanged. Its proof
assembles four components. Added five modules, all under `Sheaf.SixFunctors`:
`CoefQbarVerdierBiduality`, `CoefQbarVerdierScalars`,
`CoefQbarVerdierComparison`, `CoefQbarVerdierExactness`, and
`CoefQbarVerdierShift`. The original module imports the first four privately;
exactness imports the shift statement privately.

The biduality proof is an actual quotient calculation: a common-stage double
application of mapAt cancels against the two finite biduality squares, and finite
naturality gives the descended natural isomorphism. Its components are images of
finite isomorphisms, so no inverse witnesses or new functor data are chosen.
The scalar proof represents both the scalar and the arrow at their compositum,
uses tr_mapAt and opposite_transport, and moves multiplication through the beta
factors by bilinearity. It also verifies the finite coefficient-coordinate
normalization against intrinsicQbarLinear_existsUnique. The transition square
is a generic consequence of the stage-system morphism cocycle with an identity
second extension, proved here and specialized to the normalized comparisons.

Exactness is proved from the strictly smaller shift-coherence statement:
unopposite a distinguished triangle, represent it at one finite stage, use
triangleOpEquivalence to obtain an included opposite triangle, and apply finite
exactness. mapTriangleCompIso and the shift-compatible descendedComparison
identify its image with the required triangle. This argument handles the
connecting arrow explicitly, rather than assuming that natural isomorphisms
between functors automatically respect the chosen shifts.

All six modules compiled in import order: biduality 25.7 seconds, comparison
19.8 seconds, scalars 22.6 seconds, shift coherence 0.0 seconds (cached),
exactness 18.0 seconds, and the assigned module 22.0 seconds. The assembly
needs a scoped heartbeat budget for comparing its specialized transported
category structures; its explanatory comment fixes the sole style warning.
Delivery recompiles the final texts.

No existing file outside the assigned module is changed. No shared definition,
instance, attribute or target statement changes. The unit's finite-to-rational-
to-algebraically-closed coefficient route is preserved.

## Proved and sorry left

Closed the original hole in
`WeilConjectures.CoefQbarVerdier.descended_duality_exists` (1 original hole).
Added one hole, and only one:
`WeilConjectures.CoefQbarVerdier.descended_shift_compatibility`, node
`lem-coef-qbar-verdier-shift-compatibility`, in `CoefQbarVerdierShift`.
It asks for a shift structure on the already fixed functor and exact finite
structures compatible with its fixed comparison maps. It asserts neither
Omega-linearity, biduality, transition squares, nor preservation of arbitrary
pair-category triangles. Those conclusions are established by the delivery's
proofs. Its docstring gives the evaluation-transpose construction and the
finite beta shift-square argument still to formalize.

The following new theorems have complete proofs:
`descended_biduality`, `descended_scalar_formulas`,
`descended_comparison_formula`, and `descended_exactness`.
All private helpers are proved. No definition contains a hole.
The total is 1 hole closed and 1 hole added: a decomposition, with net zero
holes removed, not a complete proof of the original import closure.

Edge cases reviewed: repeated coefficient fields and identity extensions are
included in the cocycle calculation; scalar zero and zero arrows use the same
finite linearity formula; the argument assumes neither nonzero objects nor a
nonempty scheme. The shift-coherence remainder concerns the canonical
normalized Verdier data, not an arbitrary natural isomorphism of exact functors.

## No longer needed

No module is withdrawn and no global pruning is claimed. The assigned module's
public imports remain verbatim. Removed the trial import of
`Sheaf.Paper.IntrinsicQbarCategory` from the biduality module: only the scalar
module needs that API. The scalar, transition and biduality calculations use
fields of the supplied finite data; they do not call the existence theorem
`coef_rational_verdier`. The rational operations and coefficient-descent
infrastructure remain dependencies of the shift-coherence remainder and the
finite-data definitions.

## Where the brief, the DAG or earlier work was wrong

The planned phrase "descend finite shift comparisons" contains a real
coherence obligation. `RationalVerdier.Datum.exact` supplies an existential
finite shift structure independently at each stage, while
`ExtensionProperties` records evaluation and biduality squares but no
NatTrans.CommShift instance for beta. Taking arbitrary witnesses of finite
exactness therefore does not supply the global shift comparison. The new
shift node records precisely the remaining canonical evaluation-transpose
argument; the exactness proof shows how its conclusion is used.

No source statement is weakened or disputed. The queue's current assignment
was a proof task, with one sorry, rather than a zero-hole build repair.

## New nodes

`lem-coef-qbar-verdier-biduality-component`: proved descent of the actual finite
biduality through two applications of mapAt, with the required finite
compatibility.

`lem-coef-qbar-verdier-scalars-component`: proved Omega-linearity and the exact
finite coefficient normalization, using the intrinsic quotient action.

`lem-coef-qbar-verdier-comparison-component`: proved the normalized transition
square by the generic stage morphism cocycle, including repeated fields.

`lem-coef-qbar-verdier-exactness-component`: proved preservation of all
prescribed distinguished triangles from shift coherence and their finite-stage
presentations.

`lem-coef-qbar-verdier-shift-compatibility`: the sole remaining hole, strictly
restricted to coherent shifts and finite exactness. It is the coefficient-
transport step of the same blueprint unit, not a restatement of the original
conjunction. Existing blueprint and DAG shift/duality nodes and the Mathlib
search hits were checked; none states this normalized common-stage coherence.
Each new node records actual semantic, Loogle and source searches from
searches.jsonl. No change record is required because no existing interface or
definition is changed.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.SixFunctors.CoefQbarVerdierBiduality": "283d04c88de10f8c0ac296a94e8cc9f4246068a6", "Sheaf.SixFunctors.CoefQbarVerdierBidualityDescent": "39203103c8960e61edb02aba3f51bbde1c25cd22", "Sheaf.SixFunctors.CoefQbarVerdierComparison": "f2dfe42daa79d755b56844dcf3315bc7adfe12a1", "Sheaf.SixFunctors.CoefQbarVerdierExactness": "5fa89bdeee8a2e4cebed792565f07cc168c0040c", "Sheaf.SixFunctors.CoefQbarVerdierScalars": "0f6467b33cba4e1b5a09920702f778a2298cea66", "Sheaf.SixFunctors.CoefQbarVerdierShift": "0f6a409cf351b71f7b7aaacd9149f2952d646cb1"}, "results": {}, "time": "2026-10-28T07:08:45+0800", "transitive": 0, "version": 1}
```

## Second reading by Q2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
