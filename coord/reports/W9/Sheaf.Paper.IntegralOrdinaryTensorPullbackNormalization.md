## What changed

Replaced the item's existential proof hole by explicit comparison constructions and
an inverse-square argument. The two ordinary tensors are the existing signed total
tensor with its representative isomorphism restricted to flat-term K-flat complexes.
The native tensor-completion theorem gives the normalized forward maps, and its
constructibility theorem makes their components invertible. Currying their inverses
gives the required tensor coordinates.

Added IntegralOrdinaryPullbackComparison: equality of the direct coefficient maps,
uniqueness of module adjoints, and uniqueness of total left derived functors construct
the ordinary ringed pullback identification. The actual completion map is its composite
with ordinaryIntegralCompletionComparison. Its constructible invertibility is proved
from ordinaryCompletedIntegralPullback.

Added IntegralTensorPullbackAugmentation: its one remaining theorem is the forward
augmentation square for these specified maps. It constructs no comparisons and assumes
no higher-operation datum, properness, Noetherianness or invertibility of augmentation
maps. The item's proof uses tensor naturality and cancels the invertible augmentation
components to obtain the required inverse square. A proved private helper handles the
supplied functor equalities and component HEq normalization by substitution. Geometric
hypotheses follow from the given finite-type schemes over the fixed field.

The item adds proof-only imports of the augmentation module, the native tensor
comparison and constructibility modules, and DimensionFiniteTypeField for the
geometric hypotheses. Its existing definitions, public imports, and declaration
signatures remain unchanged; no other existing Lean module was edited.
The unit's statement and route are preserved. The entire item proof passed its final clean lcompile.py check in 26.7 s, with
no warnings. Both supporting modules also compiled in the sandbox import-order
check. No profiling options remain. The node overlay has no missing dependencies
and no cycle involving a delivered node.

## Proved and sorry left

Closed the original hole in
WeilConjectures.integralOrdinaryTensorPullbackNormalization
(node lem-sf-integral-ordinary-tensor-pullback-normalization).

Proved all declarations of IntegralOrdinaryPullbackComparison, including
WeilConjectures.IntegralOrdinary.directRing_eq,
WeilConjectures.IntegralOrdinary.pullIso, and
WeilConjectures.IntegralOrdinary.pullComparison_isIso.

Added exactly one hole:
WeilConjectures.IntegralOrdinary.tensorPullback_augmentation
(node lem-sf-integral-tensor-pullback-augmentation).
It is the forward component equation, before any inverse comparisons are formed.
The proof combining it with constructible effectivity is complete. This is a
one-for-one decomposition (one hole closed, one added; net zero), not a complete
proof of the mathematical obligation. The item and pullback-comparison module
have zero holes; the augmentation module has one.

## No longer needed

The declared dependency lem-sf-tensor-completion-model-existence
(Sheaf.SixFunctors.TensorCompletionModelExistence) is not needed: the native
ordinary tensor and its recorded representative comparison construct the required
ProEtaleTensorModel directly. No OpenFactorCoherence.Tensor package is chosen.

The broad lem-fix-constructible-tensor-completion wrapper is replaced by its
proved native comparison and constructible-unit components,
lem-fix-constructible-tensor-completion-comparison and
lem-fix-constructible-tensor-completion-constructible.
The forward augmentation step retains the ambient operation and canonical
completed-comparison dependencies from the original plan. No module is withdrawn.
No original import is removed: the three original public imports are used by the
statement or the ordinary-curried-comparison definition. An unnecessary new
ConstructibleTensorCompletionAssembly import was removed during development.

## Where the brief, the DAG or earlier work was wrong

The original dependencies do not state the forward tensor/pullback augmentation
square. In particular, separate invertibility and representative-normalization
results do not themselves assert this compatibility. The delivery isolates that
specific calculation, and proves the construction and inversion steps around it.
It does not repeat the existential higher-operation normalization statement.

Small cases: the new forward equation is typed without inverses of augmentation
maps, so it does not assume their invertibility outside the constructible domain.
Zero inputs and empty schemes use the same signed tensor, quotient maps and zero
shifted Roos components. Identity pullback uses the same adjunction-normalized map.

## New nodes

lem-sf-integral-ordinary-pullback-comparison records the concrete pullback comparison
and its proved constructible invertibility. It uses the existing ordinary completion
comparison rather than a choice from an existence statement.

lem-sf-integral-tensor-pullback-augmentation records only the forward augmentation
component equation and its full representative/strict-tower proof in words.
Its explicit tensorModel packages the already constructed native ordinary tensor;
TensorAugmentationNormalized retains the full chain-map normalization. This node
contains the delivery's only sorry. Mathlib searches were run with LeanFinder,
Loogle and indexed grep, followed by local source searches. No change record is
needed because no existing shared interface changes.

## Second reading by W9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
