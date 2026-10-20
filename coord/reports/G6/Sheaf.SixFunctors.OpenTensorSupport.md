## What changed

The target theorem `derivedTensor_openSupported` is proved by exhibiting the explicit
adjoint transpose of the normalized tensor comparison and applying `Functor.essImage.ofIso`
to the canonical extension-by-zero object. The proof imports the new auxiliary module
`Sheaf.SixFunctors.OpenTensorSupportAux`.

## Proved and sorry left

Closed the original sorry in `derivedTensor_openSupported` (1 of 1 target declarations).
The auxiliary declaration `tensor_open_extension_comparison_isIso` remains as one split-off
sorry. It is a strictly narrower geometric comparison statement whose explicit map is the
missing projection-formula construction; the target proof combines it with the categorical
essential-image API.

## No longer needed

No public import was removed. The target proof no longer directly uses the ten original
proof-dependency nodes (`def-pc-flat-sheaf-modules`, `def-pc-kflat-complex`,
`def-pc-tensor-complex-sheaves`, `lem-pc-kflat-resolution`,
`lem-pur-site-restriction-module-adjunction-exact`, `lem-weil-pbc-diagram-site-realization`,
`lem-weil-pbc-left-adjoint-preserves-colimits`,
`lem-weil-pbc-ringed-pullback-preserves-kflat`,
`lem-weil-pbc-ringed-slice-extension-tensor`, and
`lem-weil-pbc-site-derived-tensor-descent`). They remain recorded as dependencies of the
auxiliary node because they are the route for proving that comparison.

## Where the brief, the DAG or earlier work was wrong

The original proof steps conflate the geometric construction of the open tensor comparison
with the final essential-image argument. The available `Operations` interface contains the
normalized tensor comparison but no field asserting its projection-formula invertibility.
Consequently the final target can be proved categorically only after isolating that missing
comparison as a separate theorem. The target statement and all existing declarations are
unchanged.

## New nodes

Added `lem-sf-open-tensor-support-aux` for
`SheafOfModules.OpenTensorNormalization.tensor_open_extension_comparison_isIso` in
`Sheaf.SixFunctors.OpenTensorSupportAux`. Its statement is strictly narrower than the target:
it asserts invertibility of the concrete adjoint-transpose map, while the target only asks for
essential-image membership.

## Second reading by G6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
