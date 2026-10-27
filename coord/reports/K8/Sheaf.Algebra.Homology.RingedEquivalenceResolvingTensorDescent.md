## What changed

Completed the transfer proof in `Sheaf.Algebra.Homology.RingedEquivalenceResolvingTensorDescent`.
The construction transports the supplied source symmetric tensor and its K-flat model maps
across the exact coefficient equivalence. It proves the flat-term localization using the
existing fraction restriction theorem and transferred K-flat resolutions. It derives the
prescribed tensor and unit normalization from the monoidality of the existing exact-functor
factorization isomorphism. An identity comparison obtained from monoidal localization proves
independence of the target tensor presentation.

Private helpers cover restriction of monoidal equivalences, coherent model functors on
complexes and homotopy classes, localization, normalization uniqueness, and the identity
comparison between models. Native module-sheaf instances are cached by reducible abbreviations
with local instance attributes, avoiding repeated sheafification searches. Native homotopy
tensor and braiding instances are cached in the same way. The existing
countable-complex and ringed-complex monoidal instances also have higher priority locally
to avoid repeated construction of the same total tensor. The private model identity is
irreducible after its unit and tensor equations are proved, so later coherence arguments
use those equations without expanding the localization construction. The change record is
`coord/changes/k8-ringed-equivalence-instance-caches.md`. Existing public signatures and the
source-library modules are preserved. The node proof now describes the implemented route.

## Proved and sorry left

The original module contains one hole, in
`CategoryTheory.RingedEquivalenceTensorDescent.ringed_equivalence_resolving_tensor_descent`.
The submitted proof closes that hole, including resolving localization, coherent tensor
transfer, normalization on arbitrary K-flat pairs, uniqueness, and model independence.
Holes added: zero. Holes remaining in the submitted module: zero. No statements are split off.
Dependencies that already contain `sorry` are used as allowed by the stage-3 brief.

## No longer needed

Removed the private import `Sheaf.Algebra.Homology.RingedDerivedTensorNative` and the proof
dependency and obsolete `tool_uses` entry `lem-sf-ringed-derived-native-tensor`. The supplied `TensorModel` already includes
the source model maps and their native associator, unit and symmetry equations, so rebuilding
the source tensor is unnecessary for this transfer. This does not withdraw that module or any
source-library declaration and makes no claim about its other consumers.

Removed redundant direct imports of `Mathlib.Algebra.Homology.DerivedCategory.Fractions`,
`Mathlib.Algebra.Homology.ShortComplex.PreservesHomology`,
`Mathlib.CategoryTheory.Localization.Predicate`, and
`Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`; the retained imports
already provide their declarations. The K-flat resolution theorem remains a proof dependency.

The old plan's separate three- and four-variable localization checks are replaced by the
coherence carried by strong monoidal functors and Mathlib monoidal localization. Two-variable
localization is still used for uniqueness. All other declared proof dependencies remain.
No modules are withdrawn.

## Where the brief, the DAG or earlier work was wrong

The DAG unnecessarily reconstructed the given source tensor through its native construction.
It also planned a separate normalization extension from flat-term representatives to arbitrary
K-flat representatives. Restricting the supplied coherent model to all K-flat complexes proves
the normalization directly there. The blueprint unit route is unchanged.

Continuation reset the launcher's reference clock: the original dispatched start was
1792676507.960791 (2026-10-22 13:41 UTC), while `.budget` now records start
1792696749.9676664 (2026-10-22 19:19 UTC), and the latest continuation records
1792730173.9383695 (2026-10-23 04:36 UTC). No budget metadata was edited by this worker.
The compile-service outage and later busy-server responses delayed verification; they were
retried under the brief's instructions.

## Second reading by K8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
