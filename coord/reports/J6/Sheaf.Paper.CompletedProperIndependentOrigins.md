## What changed

Proved `AlgebraicGeometry.Scheme.completedProperIndependentOrigins` in
`Sheaf.Paper.CompletedProperIndependentOrigins` without changing its signature.
For arbitrary ambient endpoints, assemble the projection, strict-exchange and
inverse direct-image/Rlim natural transformations and take their naturality equation.
For complete inputs, use the existing intrinsic-to-tower implication and the fourth
normalized finite evaluation equation. Cancel its corner isomorphism, then apply
levelwise homology and `DerivedCategory.isIso_iff` to obtain the strict isomorphism.
Functoriality makes the ordered completed composite invertible. Its equality with
`completedBaseChangeMap` is `rfl`.

The existing `CompleteProetale` proof contains the same detection argument privately;
its public theorem requires compatible origins, so it is not used here. The existing
`CompletedExchangeCoherence` naturality theorem requires completeness and witnesses;
its natural-transformation construction works unrestrictedly and is assembled here.
Updated the item's proof plan and direct proof dependencies to the actual argument.
No other Lean module changes and no new declarations or nodes are introduced.

Validation: the full proof compiled remotely, then compiled again after removing the
unused imports (2.7 seconds, exit 0). Edge cases retain the actual constructions:
zero H, arbitrary/noncomplete naturality endpoints, independently varying origin
bounds, and identity squares impose no additional hypotheses. No origins were selected
from an existence theorem. Delivery preflight supplies the declaration/axiom probe.
The import-interface change is recorded in
`coord/changes/J6-completed-proper-independent-origins-imports.md`; the downstream
query and source search found zero consumer modules to adapt.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Scheme.completedProperIndependentOrigins`
(node `lem-cbc-completed-proper-independent-origins`).
Added 0 holes, split off 0 statements, and left 0 holes in the delivery.
This is a proof from existing declarations, not a claim that all transitive
mathematical dependencies are already free of sorry.

## No longer needed

Removed direct import lines:

- `public import Sheaf.Paper.AdicCoefficientDatum`
- `public import Sheaf.Paper.CompletedCompactSupportExchange`
- `public import Sheaf.Paper.IntrinsicCompletionCompleted`
- `public import Sheaf.AlgebraicGeometry.FixedEtaleOriginWitness`
- `public import Sheaf.AlgebraicGeometry.ChosenCartesianSquare`
- `public import Mathlib.AlgebraicGeometry.Morphisms.Proper`
- `public import Sheaf.Paper.CompletedPullback`
- `public import Sheaf.Paper.CompletedDirectImageLimits`
- `public import Sheaf.Paper.CompletedRlimFunctor`
- `public import Sheaf.Paper.BoundedConstructibleComplete`
- `import Sheaf.AlgebraicGeometry.ProfiniteCoefficientInverseImage`
- `import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`
- `import Sheaf.CategoryTheory.TowerDerivedEvaluationNormalization`
- `import Sheaf.Paper.PerfectProjectionFormula`
- `import Sheaf.Paper.CondensedAmbientExchange`
- `import Sheaf.Paper.ProjectionMateExact`
- `import Sheaf.Paper.KoszulReconstruction`
- `import Sheaf.Paper.CompletedReductionFiniteEvaluationNormalization`
- `import Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction`
- `import Sheaf.Paper.FourArrows`
- `import Sheaf.Paper.FiniteReductionExchangeRectangle`
- `import Sheaf.Paper.FiniteLevelProEtaleBaseChange`

The remaining imports supply the signature, the strict normalization interface,
functor-category abelianness, and derived isomorphism detection.
Redundant direct imports do not imply that their modules vanish from the transitive
closure: several remain needed inside the retained interfaces. No module is withdrawn.

Removed direct proof dependency edges (their implementation is already encapsulated
in the retained direct-image and strict-normalization interfaces):

- `def-cbc-completed-exchange-map`
- `lem-weil-pbc-profinite-coefficient-inverse-image`
- `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`
- `lem-weil-pbc-tower-derived-evaluation-normalization`
- `lemma-weil-pbc-perfect-projection-formula`
- `def-weil-pbc-ambient-ringed-exchange`
- `lem-weil-pbc-ringed-projection-mate-exact`
- `prop-weil-pbc-koszul-reconstruction`
- `lem-weil-pbc-derived-finite-evaluation-normalization`
- `lem-weil-pbc-ring-sheaf-change-adjunction`
- `lem-weil-pbc-intrinsic-finite-exchange-rectangle`
- `thm-weil-pbc-finite-level-proetale`

The compact-support exchange definition remains a statement dependency because the
unchanged node describes the proper factor of that construction; its Lean module is
not needed to prove this factor. Koszul reconstruction is accessed through the existing
intrinsic-to-tower-completeness implication instead of being reproved here.
Removed obsolete top-level tool approvals for direct uses of:

- `lem-weil-pbc-profinite-coefficient-inverse-image`
- `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`
- `lem-weil-pbc-tower-derived-evaluation-normalization`
- `lemma-weil-pbc-perfect-projection-formula`
- `lem-weil-pbc-ringed-projection-mate-exact`
- `prop-weil-pbc-koszul-reconstruction`
- `lem-weil-pbc-derived-finite-evaluation-normalization`
- `lem-weil-pbc-ring-sheaf-change-adjunction`
- `lem-weil-pbc-intrinsic-finite-exchange-rectangle`
- `thm-weil-pbc-finite-level-proetale`

All nodes remain in the DAG. No globally unused module is asserted: the project's
closure ledger determines that after landing. The compact-support unit route is kept:
this remains the proper factor, evaluated at independent finite origins before Rlim.

## Where the brief, the DAG or earlier work was wrong

No false statement or tool failure was found. The earlier plan rederived projection
invertibility, ambient strict naturality and finite normalization that the published
interfaces now provide. Direct image preserving completeness is not required in the
last step: `completedBaseChangeMap` is definitionally `completedExchange`. Its retained
hypotheses do not alter the ordered formula. The original docstring remains unchanged;
the updated DAG records which parts of that plan are used through existing interfaces.

## Second reading by J6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
