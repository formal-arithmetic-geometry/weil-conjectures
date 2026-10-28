## What changed

Replaced the body of `WeilConjectures.IntegralFiniteExtension.homMap_isIso` with a
complete reduction to the already proved `WeilConjectures.scalarHomOrdinary_isIso`
and one new tensor-normalization statement. The original signature and public import
of `CoefIntegralFiniteExtensionCore` are preserved.

The item proves three categorical facts locally: the naturality of closed
uncurrying, the conjugation formula for the evaluation transpose under a scalar
functor isomorphism, and compatibility of the Hom equivalences with the unique
comparison of left adjoints. It then inverts the tensor square, cancels the
adjunction comparisons against their counits, and identifies the requested map
with a composite of the canonical finite-free Hom isomorphism and scalar-model
isomorphisms. The scalar-model isomorphisms and their normalization hypotheses
come from the proved `integralScalarOrdinaryModelComparison`; no data are chosen
from an unproved existence theorem.

Added `Sheaf.SixFunctors.IntegralHomScalarTensorModelComparison` and its node.
Its sole obligation is a tensor square for arbitrary inputs K,N and supplied
normalized ordinary/derived scalar identifications t,e. It neither mentions
`homMap` nor asserts invertibility of an internal-Hom comparison. Its mathematical
argument is comparison of normalized tensor representatives, independent of the
finite-free Hom calculation. The statement records the necessary pure-tensor and
cochain-counit hypotheses explicitly.

No other existing Lean module, definition, instance, public declaration or target
statement is changed. The private proof uses only the new module in addition to
the existing public Core import; an initially explored proof import of
`IntegralHomReductionComparison` was avoided by proving the needed categorical
naturality directly.

Validation: `lcompile.py --all` compiled the new module in 2.3 seconds and the
item in 14.5 seconds, without warnings or errors. Both import-direction checks
passed. The node JSON, dependency references, and 100-column limit were checked.
The delivery tool performs the required independent mechanical checks.

## Proved and sorry left

Closed the original local hole in
`WeilConjectures.IntegralFiniteExtension.homMap_isIso` by a compiling assembly
proof; there is no sorry in the item module. Added one hole:

- `WeilConjectures.IntegralFiniteExtension.scalarTensor_model_comparison`, node
  `lem-sf-integral-hom-scalar-tensor-model-comparison`, in the new module
  `Sheaf.SixFunctors.IntegralHomScalarTensorModelComparison`.

Counts: one original hole closed, one new hole added. This is a decomposition,
not an independent completed proof or a reduction of the total hole count.
The finite-free algebra is reused from an existing proved theorem, rather than
restated as another unproved invertibility theorem. The remaining tensor square
is supplied with its source, a complete natural-language argument, and a DAG node.
The statement was checked on zero inputs, the empty scheme, identity embeddings,
and rescalings of representative identifications together with their forced
counits: the adjoint comparisons cancel precisely those rescalings.

## No longer needed

No existing public import was removed and no module is withdrawn or claimed
globally pruned. The node's original direct proof dependencies
`lem-weil-finite-free-completed-scalar-comparison`,
`lem-weil-pbc-right-adjoint-preserves-kinjective`, and
`lem-weil-pbc-ringed-topoi-module-adjunction` are replaced in the proof plan by the
proved canonical scalar-Hom result, its scalar-model comparison, and the tensor
normalization square. Their underlying mathematics may still be needed
transitively by the canonical theorem and by other consumers, so they are not
reported as globally unnecessary. The node's statement dependencies are retained.

The attempted route through `IntegralHomEvaluationTransport` and manually
constructed `CoefficientTensorModels` is not imported. It would require extra
resolution and tensor-interchange adapters not needed for the delivered assembly.

## Where the brief, the DAG or earlier work was wrong

The existing finite-free calculation already proves `scalarHomOrdinary_isIso`
for arbitrary unbounded inputs. The outstanding issue for this item is the
identification of the particular evaluation transpose for the supplied tensor
presentations, not a new basis calculation. The original one-step proof plan did
not expose that normalization argument.

`tensorPresentation_counit_transport` does not directly settle this issue: its
existential closed structure has no supplied `CoefficientTensorModels`, and the
statement contains no scalar-tensor comparison square. An unspecified isomorphism
of the endpoints cannot be substituted for the required evaluation-defined map.
The delivery explicitly isolates the tensor normalization and proves the two
formal transports from it. The canonical scalar result is used as a general tool;
the unit's realized route is unchanged.

Current queue and rework records were checked, including the current server
records. The item has one original proof hole. Its quarantine record names the
old `IntegralNormalizedFamily` dependency, and no current item build-error file
was present. The delivery preserves the item's declaration and attachment and
makes no withdrawal. No target or definition repair was required.

## New nodes

`lem-sf-integral-hom-scalar-tensor-model-comparison` records the tensor square
between the normalized scalar comparison for arbitrary integral Hom presentations
and the canonical closed scalar tensor comparison transported along given t,e.
It is a strictly separate representative-normalization step, before transposition;
it has no finite-free Hom or invertibility conclusion. The three searches
(LeanFinder, Loogle and Mathlib grep) and the checked Stacks/blueprint source are
recorded in the node. Its only remaining Lean hole is the named theorem listed above.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.SixFunctors.CoefIntegralFiniteExtensionHomMapInvertibility": "9ddce66787f9ec2d51b26bec3c121755efea0b30", "Sheaf.SixFunctors.IntegralHomScalarTensorModelComparison": "4a01e96078cae46974f97124fce1c451e0e7c8bc"}, "results": {"Sheaf.SixFunctors.CoefIntegralFiniteExtensionVInvertibility": {"hash": "2981a1f19baf936f1bcaa022f34618d978bafbc3", "status": "OK"}}, "seconds": 25, "time": "2026-10-28T09:59:04+0800", "transitive": 0, "version": 1}
```

## Second reading by W3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
