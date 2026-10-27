## What changed

Filled `WeilConjectures.isomorphismPullbackScalarShift` in
`Sheaf.Paper.IsomorphismPullbackScalarShift`, preserving its statement and public imports.
Added a private proof import of the new proved module
`Sheaf.Paper.IsomorphismPullbackScalarIntegralShift`. That module privately imports
`Sheaf.Paper.IsomorphismComparisonScalarExtension` and
`WeilConjectures.CategoryTheory.DerivedCategory.Shift.ExactFunctor`.

The integral proof identifies the normalized ordinary scalar comparison with
`scalarCompletion`, proves its shift compatibility, and conjugates the ordinary derived
inverse-image tensor comparison through the specified inverse-image comparisons. The existing
scalar-extension compatibility square identifies this conjugate with the prescribed alpha.
The rational proof transfers the integral degree-one equation using the prescribed normalization
formulas, then derives compatibility in all integer degrees by addition and inverse shifts.
The integral half is the new proved theorem
`WeilConjectures.isomorphismPullbackScalarIntegralShift`; the other auxiliary lemmas are
private and proved. No shared definition or other existing module was changed.
Profiling the assembled proof exposed costly conversions between raw and cached stage
structures. Typed restriction lemmas, generic localization object/map lemmas and a single
localized integral equality reduce this cost. The complete integral portion was then moved
to its own module so each file can be checked within the unchanged per-file time limit.
The node proofs and dependency lists describe this factorization.
Validation: `lcompile.py --all` compiled both modules with zero errors and zero warnings;
local metadata checks confirmed unchanged target-item signature, exact Lean attachments,
proof-dependency unions, zero holes and the 100-character line limit.

## Proved and sorry left

Closed the one original hole: `WeilConjectures.isomorphismPullbackScalarShift`
(node `lem-pod-isomorphism-pullback-scalar-shift`). Added zero holes. No unproved statement was split off.
Also proved the new integral theorem
`WeilConjectures.isomorphismPullbackScalarIntegralShift`
(node `lem-pod-isomorphism-pullback-scalar-integral-shift`).
There are no remaining `sorry` declarations in the item or elsewhere in this delivery.
The proof uses the existing dependency declarations with their current statements.

## No longer needed

No public import, module, or node is withdrawn. No private import was removed.
The direct proof-dependency edge to `lem-pur-semilinear-scalar-localization` is unnecessary:
the proof uses the normalized rationalization API instead of reproving semilinear localization.
That node remains a transitive dependency of the scalar-extension API and is not globally pruned.
The coefficient and inclusion definition nodes remain statement dependencies; the proof does
not need separate direct edges to `def-weil-algebraically-closed-coefficients` or
`def-pod-isomorphism-coefficient-inclusions`.

## Where the brief, the DAG or earlier work was wrong

No statement correction was necessary. The existing plan is implemented without a new split.
Mathlib searches for integer shift compatibility found the zero and addition core API but no
single theorem extending a degree-one equation to all integers; a private proved helper supplies
that elementary extension. The ordinary derived comparison already has the required shift
instances in the adopted source library.

## New nodes

`lem-pod-isomorphism-pullback-scalar-integral-shift`, in
`dag/nodes/sec-poincare-duality/lem-pod-isomorphism-pullback-scalar-integral-shift.json`,
records the integral half of the argument. Its statement omits all rational-shift hypotheses
and concludes only the integral compatibility square. Its proof is complete, and the item
uses it before proving rational compatibility. It was extracted solely to keep each module
within the compilation limit; it adds no proof obligation. No change record is needed because
no existing statement, definition or public import changed.

## Second reading by G6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
