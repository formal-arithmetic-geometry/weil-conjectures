## What changed

Proved the Qlbar localizing projection formula by applying the adopted
isIso_projectionMap_of_localizingBoundedConstructible theorem. The proof converts the
constant-model and adopted bounded constructibility predicates using finite coefficient
descent, identifies the two localizing-closure universe conventions, supplies proper
pushforward, coproduct preservation, pullback and tensor closure, and obtains membership
of both endpoints together with invertibility of the canonical mate.

Factored the repeated representative formula through tensorRepresentativeFormula and
constructed moduleObjectDerivedTensorComparison directly as leftDerivedUpperStarTensor.
The proved normalization theorem verifies the original generator and counit formulas;
uniqueness identifies this construction with the previous selected witness. The actual
projection mate is unchanged mathematically. The forced consumer edit changes only its
proof of IsIso to use the new normalization theorem. Existing public imports and target
signatures are retained verbatim.

Change records:
- coord/changes/P5-rational-tensor-representative-formula.md
- coord/changes/P5-rational-comparison-construction.md

## Proved and sorry left

Closed: AlgebraicGeometry.ProEtale.CondensedRing.isIso_projectionMate_localizing_padicAlgCl.

Remaining existing hole:
AlgebraicGeometry.ProEtale.CondensedRing.isIso_projectionMate_localizing_finiteExtension.

Original holes: 2. Closed: 1. Added: 0. Remaining: 1. All helper proofs are complete.
The item module compiled remotely in 51.5 seconds. Consumer and final delivery checks
are run by the delivery tool.

## No longer needed

For the implemented Qlbar case, the adopted LocalizingProjection proof already supplies
exactness and shift compatibility and performs determination first in A, then in B.
Separate reconstruction from lem-sf-triangulated-right-adjoint,
lem-weil-pbc-adjunction-shift-compatibility-unique and
lem-weil-pbc-ringed-projection-mate-exact is unnecessary for that case.
The finite-extension case remains open and retains its original DAG plan and dependencies.
No module is withdrawn and no global pruning is claimed.

## Where the brief, the DAG or earlier work was wrong

The adopted source library already proves the formal two-variable localizing extension.
Its projectionMap uses the published internal-module tensor comparison, while the item
originally selected the same map from a unique-characterization theorem. Their identity
is required to use the adopted extension. Repeatedly elaborating the full concrete
representative formula and the generic one made this interface expensive. Factoring the
identical formula and retaining named derived constructions addresses that issue.

Both existing target signatures were compared with the repository and are unchanged.
The unit realized statement and proof-step lists are empty; the unit route through
bounded projection and determination in the two variables is preserved.

## Forced adaptations

Sheaf.Paper.ProEtaleProjectionExchangeMaps explicitly obtains the IsIso witness for the
old chosen comparison using exists.choose_spec.2. With the comparison constructed
directly, that proof has the wrong subject. Replace only this proof by
(moduleObjectDerivedTensorComparison_normalized Λ f).2; the signature, map and all
other data are unchanged. The delivery tool records the independent counterfactual check.

## Second reading by P5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
