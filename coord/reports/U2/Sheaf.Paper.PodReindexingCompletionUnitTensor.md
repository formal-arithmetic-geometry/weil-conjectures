## What changed

Replaced the remaining proof hole in `Sheaf.Paper.PodReindexingCompletionUnitTensor`
with a complete assembly of normalized completion and tensor data. The existing
ambient completion proof and all existing declaration signatures are unchanged.

The assembly first uses `podReindexingCompletionUnit` at each isomorphism, then
extends that same datum to tensor data, adds section-normalized family coherence,
and applies separate signed-shift, coefficient-transition and substitution steps.
The choices occur only locally in the proof of an existence theorem. No definition
or instance is populated with data from a mere existence theorem.

The constructible-input isomorphism is proved from the ambient complete-input
result: choose an auxiliary prime larger than l, construct its finite-field datum,
and use `sfDerivedComplete_iff_legacy` on the constructible object's completeness
property. This adds the proof-only import `SfDerivedCompleteLegacyComparison`.
Five proof-only imports contain the five remaining, strictly partial statements.
Each is a new public theorem in its own module, with a DAG node and a complete
representative-level proof in words. The parent node now records the actual
assembly route rather than retaining the unrealized tensor proof plan.

## Proved and sorry left

Closed the sole original hole:
`WeilConjectures.podReindexingCompletionUnitTensor`.
The item's module has zero remaining holes; its previously proved
`WeilConjectures.podReindexingCompletionUnit` remains proved.

Added five holes, one per construction step:

- `WeilConjectures.podReindexingTensorConstruction`
  (`lem-pod-reindexing-tensor-construction`): extend a fixed normalized completion
  datum to the strict tensor tower and its canonical completed realization.
- `WeilConjectures.podReindexingTensorFamilyCoherence`
  (`lem-pod-reindexing-tensor-family-coherence`): supply only the identity and
  composition isomorphisms and coherence laws for already supplied normalized
  completion and tensor assignments.
- `WeilConjectures.podReindexingTensorSignedShifts`
  (`lem-pod-reindexing-tensor-signed-shifts`): signed shifts of fixed normalized
  completion and tensor data.
- `WeilConjectures.podReindexingTensorCoefficientTransition`
  (`lem-pod-reindexing-tensor-coefficient-transition`): compare fixed data at E and L across
  one coefficient embedding with its precise scalar squares. The parent constructs
  Dprime and Tprime from the ambient and tensor construction lemmas itself.
- `WeilConjectures.podReindexingTensorSubstitution`
  (`lem-pod-reindexing-tensor-substitution`): compare expression models with fixed
  normalized primitives and apply substitution to those primitives.

This is a decomposition, not a net proof gain: one hole closed, five added
(net minus four). No new theorem restates the original whole existential family
assertion. In particular none of the fixed-datum steps supplies a coherent family,
and the coherence step assumes completion and tensor assignments already exist.
The final assembly and the constructible-completeness bridge are real Lean proofs.

## No longer needed

No original Lean import was removed. The existing ambient proof still uses all
four original proof-only imports. Public imports remain unchanged.

The parent's direct proof dependencies are now the six dependencies of its
existing ambient proof, the five new partial construction steps, and
`lem-sf-derived-complete-legacy-comparison`. The following old direct dependencies
are discharged inside the new construction steps or already inside the ambient
proof; they are not asserted to be globally unused:
`lem-pod-reindexing-hom-resolution-model`,
`lem-coef-derived-system-evaluation-calculus`, `def-pur-kinjective-complex`,
`lem-pc-kflat-resolution`, `lem-weil-proetale-countable-products-exact`,
`lem-cbc-exact-product-functor-strict-limit`,
`lem-weil-finite-free-completed-scalar-comparison`,
`def-pur-integral-derived-operations`, `lem-pur-kflat-change-of-rings`,
`lem-pur-kflat-total-tensor-model`, `def-pc-tensor-complex-sheaves`,
`lem-pur-integral-operations-well-defined`,
`def-pur-completed-pullback-tensor-comparison`,
`def-pur-finite-pullback-tensor-comparison`,
`lem-pur-isomorphism-inverse-image-tensor-hom`, and
`lem-pur-completed-operation-tower-substitution`.
Their obsolete parent `tool_uses` entries are removed; normalized reconstruction
is retained. No module is withdrawn or claimed pruned, and no source-library
file is edited.

## Where the brief, the DAG or earlier work was wrong

The inherited source path places the dual-Tate proof under `sk-lem-finite`.
The current blueprint places it under `sk-thm-frobenius`; the new nodes cite the
current `literature/blueprint/latest/` file. The original source field is preserved.
The unit record `sk-def-weil` has no realized statement or proof-step nodes to
bypass. The same original Steps 1 and 5 remain the source of all partial steps.

Existing generic dependencies do not directly state the remaining combined
normalized tensor/family/scalar/shift/substitution assertions. The refinement is
therefore explicit rather than treating generator or finite-evaluation equality
as equality of arbitrary derived strict-system morphisms. Whole-system and both
Roos-coordinate equalities remain requirements of the new lemmas. The substitution
interface also demands literal equality of selected calculus/closed-structure
presentations. Its new lemma retains these pins; the proof must establish them
for the selected calculus, not replace equality by an arbitrary isomorphism.

Edge cases checked against the new statements and proof plans: empty schemes,
zero tensor inputs, the identity isomorphism and its composites, every integer
shift including zero and negative shifts, identity coefficient embeddings, and
incomplete ambient inputs (where no unit invertibility is asserted).

## New nodes

`lem-pod-reindexing-tensor-construction`, module
`Sheaf.Paper.PodReindexingTensorConstruction`, isolates the tensor summand,
quotient-transition and Roos realization construction (old tensor proof steps).

`lem-pod-reindexing-tensor-family-coherence`, module
`Sheaf.Paper.PodReindexingTensorFamilyCoherence`, isolates identity, composition
and tensor structural equations for supplied comparisons (old last proof step).

`lem-pod-reindexing-tensor-signed-shifts`, module
`Sheaf.Paper.PodReindexingTensorSignedShifts`, isolates both tensor shift signs,
the actual reduction/limit shift squares and the signed Roos models.

`lem-pod-reindexing-tensor-coefficient-transition`, module
`Sheaf.Paper.PodReindexingTensorCoefficientTransition`, isolates finite-free scalar
extension between fixed normalized data at both fields and its own completion/tensor
normalization squares. The parent separately constructs the target-field data.

`lem-pod-reindexing-tensor-substitution`, module
`Sheaf.Paper.PodReindexingTensorSubstitution`, isolates the compatibility of
completed-expression models with these fixed primitive data.

All inherit chapter `sec-poincare-duality` and unit `sk-def-weil`. Each records
LeanSearch, LeanFinder and Mathlib grep searches, its exact Lean statement, source,
proof in words, and any generic tool uses requested for independent review.
No statement or definition was changed, so no change record is needed.

## Second reading by U2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
