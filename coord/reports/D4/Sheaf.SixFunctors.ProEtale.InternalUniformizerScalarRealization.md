## What changed

The item now proves `uniformizer_scalar_realization` from one ordinary-module scalar
comparison. Its statement and three original public imports are unchanged. Private
proof imports supply the proved constant-quotient kernel formula and the proved
injectivity of regular constant scalars.

The proof transports the actual quotient kernel through a commuting square of ring
isomorphisms, proves regularity from the coefficient DVR and constant sheafification,
and proves that the prescribed scalar transport preserves powers. A separate proved
calculation extends an ordinary right-unitor scalar equation to the total tensor of
an arbitrary cochain complex. It uses Mathlib's degreewise inverse-right-unitor,
single-complex map, and total-tensor coproduct-inclusion formulas. It imposes no
boundedness, flatness, or nontriviality hypothesis on section rings.

The new module `Sheaf.SixFunctors.ProEtale.OrdinaryUniformizerScalarComparison` states
the remaining single-scalar equation on ordinary modules, with compatible coefficient
and first-residue comparisons. Only the item, its node, this new module and its node
are changed. No existing shared interface or source-library declaration is changed.

Validation: the final ordinary-comparison module compiled in 39.2 seconds, and the
final item compiled without diagnostics in 28.5 seconds through `lcompile.py`.
Profiling options were removed. The original theorem signature matches the shared
source verbatim, both Lean files satisfy the 100-character line limit, and the new
node's Lean signature matches its declaration. Added dependency edges do not lead
back to the item.

## Proved and sorry left

Closed the one original hole in
`AlgebraicGeometry.ProEtale.InternalCompletionTransport.uniformizer_scalar_realization`.
The item has zero remaining holes. Its kernel, regularity, conjugation-power,
transported-power, intertwining-power, and total-complex calculations are complete
private proofs.

Added one hole in
`AlgebraicGeometry.ProEtale.InternalCompletionTransport.ordinary_uniformizer_scalar_comparison`,
node `lem-sfb-ordinary-uniformizer-scalar-comparison`. Its proof is exactly `by sorry`,
and its docstring and node give the source and the full ordinary-module argument.
There are no other new holes and no holes in definitions.

This is a decomposition: one upper hole is closed and one strictly smaller ordinary
comparison is added, for net zero holes among the changed statements. It is not claimed as a completed proof of the
coefficient action. The kernel and regularity assertions, passage to all positive
powers, and total-complex equation are supplied by actual Lean proofs rather than
being repeated in the new obligation.

## No longer needed

No modules are withdrawn and no original public imports are removed. No transitive
pruning is claimed.

The item's direct proof no longer needs
`lem-sfb-internal-discrete-quotient-comparison`,
`def-sfb-integral-constant-model-realization`, or
`lem-pe-internal-section-tensor-comparison`: their ordinary coefficient and tensor
normalizations belong to the remaining ordinary comparison. They remain dependencies
of that new node and are therefore not pruned from the project.

The completion-section transport, quotient-tower model, principal-reduction calculus,
and singleton-Koszul-cone nodes remain statement dependencies, because the theorem
still uses their prescribed definitions. Their theorem-level conclusions are not
additional proof assumptions of the new argument.

The total-complex portion of `lem-pe-internal-section-tensor-comparison` is unnecessary
for this proof: the ordinary scalar equation lifts to complexes using Mathlib's
explicit right-unitor and coproduct formulas. Its ordinary-module portion remains
needed by the residual node. No completion-triangle or strict-completion-presentation
comparison is imported for the elementary power calculation.

## Where the brief, the DAG or earlier work was wrong

The original plan treated identification of the prescribed continuous uniformizer
with the constant section as part of following the transport. The quotient comparison
alone states a commuting quotient square; it does not state the action equation for
`DerivedNakayama.scalarOnModules` after the two restrictions of scalars. The ordinary
tensor comparison supplies normalized unit and tensor coherence, but also does not
directly state this coefficient-specific equation. The remaining node isolates that
ordinary normalization step instead of assuming it follows from a quotient square.

No statement was found false and no statement or definition was weakened. The unit's
uniformizer/Koszul reduction route is retained.

A dependency audit also found an existing cycle outside this packet:
`lem-pc-ring-hom-extension-differential` ->
`lem-pc-ring-hom-extension-differential-adjacent` ->
`lem-pc-ring-hom-extension-differential`. It is already reachable from the original
item through its quotient-comparison dependency. Neither node is changed here; none
of this packet's added edges has a path back to the item.

## New nodes

`lem-sfb-ordinary-uniformizer-scalar-comparison` is the ordinary single-scalar portion
of the original proof's coefficient comparison step. It introduces compatible integer
and first-residue ring comparisons and states the right-unitor equation for one
uniformizer on an ordinary module. It contains no ideal equality, regularity claim,
power formula, cochain complex, or totalization. Its natural-language proof records
the constant-section normalization, point comparison, relative module action,
restrictions of scalars, and ordinary section tensor comparison. The empty scheme
and zero modules give equations of unique maps; no section-ring nontriviality or
module flatness is required. Mathlib and blueprint searches found no exact duplicate.
There is no change record because no existing statement or definition changes.

## Second reading by D4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
