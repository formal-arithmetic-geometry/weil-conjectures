## What changed

Proved `WeilConjectures.podAmbientReindexingTensor_existsUnique` with its original
statement. The ordinary completed-module tensor comparison is the inverse of the
normalized ringed-pushforward tensorator. Its naturality follows by cancellation,
and its section formula follows from the tensorator's pure-tensor formula.
The signed total-tensor comparison transports the K-flat acyclic tensor test using
the exact inverse equivalence and its counit. `modelOfOrdinary` then descends this
comparison to the prescribed derived tensor models. Local pure-tensor generation
and `tensorComparisonModel_unique` prove uniqueness of the ambient comparison.

The two supporting specializations are in new modules
`Sheaf.Paper.PodCompletedOrdinaryTensor` and `Sheaf.Paper.PodCompletedKFlatTransport`.
No existing statement, definition, public import or attribute changes. The main
system-reindexing theorem is the untouched remaining proof obligation; the brief
permits delivery of one completed hole in a module with several holes.

Validation: `lcompile.py --all` compiled all three sandbox modules in import
order with exit code 0 and no warnings. The delivery tool performs the final
preflight and axiom checks.

## Proved and sorry left

Original holes: 2. Closed: 1. Added holes: 0. Split-off unproved statements: 0.

- Closed: `WeilConjectures.podAmbientReindexingTensor_existsUnique`.
- New proved helper: `WeilConjectures.podCompletedOrdinaryTensor_exists`, node
  `lem-pod-completed-ordinary-tensor`.
- New proved helper: `WeilConjectures.podCompletedKFlatTransport`, node
  `lem-pod-completed-kflat-transport`.
- The only remaining `sorry` is the unchanged
  `WeilConjectures.podReindexingSystemHomReductionSquare`, node
  `lem-pod-reindexing-system-hom-reduction-square`.

## No longer needed

Removed unused direct proof imports from the item:

- `Sheaf.Paper.PodReindexingHomResolutionModel`
- `Sheaf.Paper.PodReindexingEvaluationShiftComposition`
- `Sheaf.Paper.RingedPullbackHomEvaluationComparison`
- `Sheaf.CategoryTheory.SequenceAdjunctionCochainTransposes`
- `Sheaf.CategoryTheory.SequenceProjectionDerivedAdjunction`
- `Sheaf.CategoryTheory.SequencePushforwardLimitProjections`
- `Sheaf.Algebra.Homology.ExactMonoidalEquivalenceTotalKFlat`
- `Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal`
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed`
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp`

No module or node is withdrawn: these dependencies remain in the retained plan
for the still-open main system theorem. In particular, the ambient proof avoids
using `podReindexing_resolution_preservation` with unavailable residue-field
hypotheses. Its unrestricted completed-coefficient argument instead uses the
already proved exact equivalence, normalized pairing, signed-total descent and
model uniqueness. The item node records this additional ambient route while
preserving the main theorem's nine-step plan and the unit route.

## Where the brief, the DAG or earlier work was wrong

The retained report incorrectly said that the ambient proof did not compile and
that the two helpers were both proved while their bodies were `sorry`. This
session replaced both helper holes with Lean proofs and repaired the local
site-equivalence name and inverse-additivity instance.

`podReindexing_resolution_preservation` assumes residue-field invertibility,
whereas the ambient theorem is before those hypotheses. It cannot be applied
there directly. The completed-module equivalence and normalized tensorator have
the required unrestricted hypotheses. No mathematical statement was corrected.

The existing proved private generic helpers `pushforward_tensor_isIso`,
`exactTensorTotalIso`, `modelOfOrdinary`, `acyclic_map_iff` and `acyclic_of_iso` are
accessed through proof-only `import all` imports. The generic pairing, exact
transport, tensor-evaluation and uniqueness nodes are tools for the same ambient
construction; they do not replace the unit's route.

## New nodes

`lem-pod-completed-ordinary-tensor`: the completed-module ordinary tensor
comparison, natural in both inputs and normalized on every local pure tensor.
The proof specializes the existing invertible normalized pushforward tensorator.

`lem-pod-completed-kflat-transport`: preservation of the K-flat acyclic tensor
test on completed-module complexes. The proof uses the signed-total comparison,
exactness and the termwise counit. Both new statements have complete Lean proofs;
neither introduces a `sorry`. No change record is needed: existing interfaces
are preserved, and all removed imports are proof-only.

## Second reading by M7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
