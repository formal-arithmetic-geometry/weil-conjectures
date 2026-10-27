## What changed

Replaced the body of `AlgebraicGeometry.Scheme.pur_integral_twist_line_inverse_image`
with an assembly from normalized coefficient pushouts, the canonical root-limit
comparison, and conditional integral tensor transport. All six existing public
signatures and their definitions are unchanged. Both field-inclusion squares are
proved directly: quotient projections determine the coefficient square, and tensor
induction plus sheafification and adjunction determine the line square.

Added three modules: `PurBaseCompletionPullbackIso` proves the base coefficient
comparison invertible using the existing finite constant-tower theorem;
`PurRootTowerPreservation` isolates the cyclotomic free-tower specialization;
`PurIntegralTensorTransport` isolates specialization of tensor transport to the
recorded line and its completed action. Updated the parent node's proof fields.
No source-library module or target statement is changed.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.pur_integral_twist_line_inverse_image` (one original hole).
This is a decomposition, not an unconditional proof: two strictly smaller argument
steps remain as new public theorem holes:

- `AlgebraicGeometry.Scheme.pur_root_tower_preservation`, node
  `lem-pur-root-tower-preservation`: only preservation of the cyclotomic limit.
- `AlgebraicGeometry.Scheme.pur_integral_tensor_transport`, node
  `lem-pur-integral-tensor-transport`: given normalized invertible coefficient/root
  comparisons, construct the integral tensor comparison and its semilinearity.

The new theorem
`WeilConjectures.CompletedCoefficientNormalization.pur_base_completion_pullback_isIso`
(node `lem-pur-base-completion-pullback-iso`) has no hole. The parent has no remaining
hole. Added holes: two; closed original holes: one. The scalar-map normalization
`WeilConjectures.twistScalarMaps_existsUnique` is an existing dependency with its own
hole; it was not changed or duplicated.

## No longer needed

Removed these private proof imports from the item:

- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`
- `Sheaf.AlgebraicGeometry.ProEtaleCoefficientComparisonsPullback`
- `Sheaf.AlgebraicGeometry.ProEtaleIntegralCoefficientLimit`
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`
- `Sheaf.AlgebraicGeometry.ProEtaleRootsOfUnitySheaf`
- `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`
- `Sheaf.CategoryTheory.ConstantLeftModuleInverseImage`
- `Sheaf.CategoryTheory.ModulePullbackTensorIso`
- `Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted`
- `Sheaf.Paper.PurInverseImageCompatibleFreeTower`
- `Sheaf.Paper.TateTwistLocallyFree`

The parent no longer directly invokes the finite-field-specific integral-limit and
coefficient-pullback interfaces; the base-only finite constant-tower route supplies
its coefficient invertibility. The compatible-free-tower, localization, and generic
tensor-transport nodes remain needed through the two split steps, so they are not
claimed as globally pruned. Existing public imports are preserved. No module is
withdrawn, and no whole-library module is claimed pruned. Removed obsolete parent
`tool_uses` approvals for `det-prop-sfb-qlbar-colimit-x-integral-limit`,
`det-prop-sfb-qlbar-colimit-x-pullback`, and
`lem-weil-pbc-ringed-topoi-module-pullback-tensor`; the current assembly does not
use these interfaces. The remaining approvals retain their original order.

## Where the brief, the DAG or earlier work was wrong

The original coefficient route uses an interface restricted to finite intermediate
fields of the selected algebraic closure, whereas the item allows any finite
extension in the scheme universe. The normalized coefficient presentation supplies
maps and commuting squares for the required fields but does not itself assert that
its base comparison is invertible. The finite constant-ring tower preservation
API proves precisely that missing base case, without changing any statement.

The abstract compatible-free-tower theorem and semilinear tensor transport use
small-site encodings and different concrete module presentations. Their
specialization requires transport through small models, universe lifts, underlying
sheaf comparisons, and factor-switching of the recorded scalar extension. These
are the two explicit remaining steps; neither is the original five-map theorem
under another name. Edge cases checked mathematically: empty schemes, identity
base change, l=2, E=Q_l, E=F and ramified field inclusions. No nonemptiness or
unramifiedness hypothesis is used.

## New nodes

`lem-pur-base-completion-pullback-iso` is the proved base-only comparison step.
It uses the finite constant-tower preservation theorem and projection uniqueness.

`lem-pur-root-tower-preservation` is the free-tower specialization for the actual
cyclotomic diagram, with a complete source proof in its docstring and node.

`lem-pur-integral-tensor-transport` is the conditional specialization of normalized
semilinear tensor transport to the actual completed-action line. It supplies none
of the coefficient/root maps and none of the inclusion squares.

Searches: LeanFinder, Loogle, grep and LeanSearch queries are recorded in
`searches.jsonl` and in each new node. Blueprint searches for root inverse limits,
completed coefficient tensor normalization, integral tensor transport and base
completion pullback found no exact blueprint node. The nearest blueprint ancestor
is `prop-weil-twist-preserves`, retained in all three new node references.

No change record is needed: no existing definition or statement was changed.

## Second reading by W3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
