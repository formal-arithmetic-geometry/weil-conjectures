## What changed

Reduced the integral coefficient comparison to the existence of a normalized tensor-completion
model, and the uniqueness of its actual chain augmentation. The proof explicitly constructs
the isomorphism between ordinary models by product localization, verifies compatibility of chi,
uses ordinary comparison uniqueness to identify the transported maps, and inverts the two chi maps.
Categorical reassociation, cancellation and coefficient-square transport are proved in generic
private helpers, so their concrete applications do not unfold the large coefficient presentation.
The integral_identity equality supplies the literal underlying endpoints. Full-subcategory lifting
and evaluation at one existing model then prove integral_existsUnique, with its original signature
and its normalization for every model.

Added the existence and chain-uniqueness modules, plus the proved support modules
ProjectionTensorNormalization and ProjectionTensorModelComparison. The latter two extract the
previously compiled normalization, naturality and model-comparison proofs after a final compile
exceeded the 60-second limit. The original good, totalIso_naturality, normalizedTensorDescent and
completion_isIso declarations retain their signatures and delegate to the same extracted proofs.
No existing definition, public signature, exported attribute or public import was changed.
A local reducibility annotation exposes the packaged completed coefficient ring only while checking
the new comparison proofs. The rework attachment and all original declarations are preserved.

Validation: lcompile.py --all compiled all five Lean files without warnings after extraction.
Every requested file passes the compile service's 60-second acceptance check. The initial large
packet exceeded that limit, which motivated the extraction; it was not pushed. All temporary
profiling options are removed.

## Proved and sorry left

Closed the original hole in
WeilConjectures.CompactSupportCoefficientTensor.integral_existsUnique
(node def-sf-projection-tensor-coefficient-comparison) by the explicit assembly described above.
The original hole in
WeilConjectures.CompactSupportCoefficientTensor.rational_existsUnique
remains unchanged, with its original source and complete proof plan.

The delivery adds the hole
WeilConjectures.OpenFactorCoherence.tensorCompletionModel_nonempty
(node lem-sf-tensor-completion-model-existence). Its statement concerns only existence of an
ordinary tensor/completion presentation, with no coefficient equivalence or integral comparison.
The existing ambient operation-model theorem supplies the underlying normalized comparison;
the remaining task is the bridge from that shared ambient presentation to the Tensor record.

WeilConjectures.OpenFactorCoherence.tensorCompletionChain_unique
(node lem-sf-tensor-completion-chain-uniqueness) is proved by total-summand, local tensor and product
extensionality, followed by the mapping-cocone identity decomposition.
The new public helpers
WeilConjectures.ProjectionTensorNormalization.normalizedTensorDescent and
WeilConjectures.ProjectionTensorModelComparison.models_comparison are also fully proved;
the extraction adds no holes.
This is a decomposition of the integral hole, not a net closed-hole claim.

## No longer needed

No modules or nodes are withdrawn. The item's direct proof imports of
RingIsomorphismTensorTransport and TensorPullbackRepresentativeDescent move to
ProjectionTensorNormalization. Its direct TensorCompletionChainUniqueness import moves to
ProjectionTensorModelComparison. These dependencies remain in the closure and are used by the
same proofs; no mathematical dependency is claimed pruned.
The unit's statement and route remain unchanged.

## Where the brief, the DAG or earlier work was wrong

The previous DAG recorded that the integral and rational holes were unchanged rather than giving
Lean-level intermediate interfaces for the integral argument. The updated proof records the actual
localization and endpoint assembly. Nonvacuity of the normalization needs a Tensor model, while the
constructibleTensorCompletion theorem directly returns an ordinary functor, chain and transformation;
it does not itself package the ambient completion isomorphism required by Tensor. The new existence
lemma exposes exactly this bridge to the already recorded ambient operation comparison.

OpenFactorCoherence and OpenFactorProjectionRealization cannot supply a model here by import:
tools/import_direction.py reports that each already reaches this item, so either import would close
a cycle. No dependency was removed to bypass that restriction.

Edge cases checked: empty schemes and zero complexes use the same tensor, product and cocone
universal properties; the chain uniqueness argument never assumes a nonzero coefficient or
nonempty summand. The full-subcategory lift uses exact object equalities from integral_identity,
not arbitrary isomorphisms. Both quotient and zero shifted coordinates are retained.

## New nodes

lem-sf-tensor-completion-chain-uniqueness, in
Sheaf.SixFunctors.TensorCompletionChainUniqueness: the two prescribed coordinates determine the
chain map, independently of coefficient transport. Its proof evaluates the first coordinate on
homogeneous local pure tensors and uses mappingCocone.id_X for the two-coordinate reconstruction.

lem-sf-tensor-completion-model-existence, in
Sheaf.SixFunctors.TensorCompletionModelExistence: a normalized tensor/completion model exists on
the qcqs scheme with the given invertible prime. Its source and full proof plan are in the docstring
and node. This is a strict subargument, independent of the integral coefficient equivalence and of
the comparison to be lifted.

lem-sf-projection-tensor-normalization-descent, in Sheaf.Paper.ProjectionTensorNormalization:
the already proved descent wrapper with inverse representative normalization. Its module also
checks the original proved private coefficient naturality and flatness helpers separately; the
item retains their interfaces as delegations. It adds no hole.

lem-sf-projection-tensor-model-comparison, in Sheaf.Paper.ProjectionTensorModelComparison:
the fully proved normalized ratio of two ordinary tensor models, compatible with chi. Its module
also checks the original constructible chi-invertibility proof as a private helper. It adds no hole.

## Second reading by D6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
