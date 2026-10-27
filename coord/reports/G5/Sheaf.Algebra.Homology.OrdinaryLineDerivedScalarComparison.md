## What changed

Proved `SheafOfModules.OrdinaryLineScalar.comparison_tower`. First establish the
ordinary tower equation on pure tensors using the composite scalar adjunction,
the three comparison formulas, the normalized scalar associator, and the given
signed-power tower equation. Prolong it degreewise. Paste the representative
squares with the scalar-normalization square, cancel the invertible computation
map on a flat-term K-flat model, and extend by naturality along a K-flat resolution
to every derived object.

All added helpers are private and proved. Updated node proof step 7 to record the
implementation. Existing signatures, definitions, and public imports are preserved.
Local instance priorities select the native additive structures directly, avoiding
repeated searches through abelian structures. Some proof expressions are reused
without a second elaborator expansion; the kernel checks every resulting theorem.
The private computation transformation omits an identity factor and has a proved
component equation. Existing pure-section and line-data proofs are streamlined;
see `coord/changes/G5-ordinary-line-scalar-tower-cache.md`.

## Proved and sorry left

Closed one of the two original holes:
`SheafOfModules.OrdinaryLineScalar.comparison_tower`.

One original hole remains, untouched:
`SheafOfModules.OrdinaryLineScalar.ordinary_line_derived_scalar_comparison`.

Holes added: zero. Split off: zero.

Validation: the complete module with the local instance hints checked in 48.9
seconds. The delivery checks the final version and its complete axiom closure.
The tower proof uses only `propext`, `Classical.choice`, and `Quot.sound`.
No diagnostic commands or profiling options are included.

## No longer needed

No imports, nodes, or modules are pruned. Step 7 uses ordinary tensor
extensionality and naturality along a flat-term K-flat resolution instead of a
separate application of the localization universal property. The general
localization and bilinear-universal dependencies remain needed by the untouched
comparison-construction argument in steps 5 and 6.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was needed. The proof handles every integer exponent
and arbitrary coefficient maps through the supplied signed-power and normalized
scalar comparison data; it adds no flatness or boundedness assumption.

## Second reading by G5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
