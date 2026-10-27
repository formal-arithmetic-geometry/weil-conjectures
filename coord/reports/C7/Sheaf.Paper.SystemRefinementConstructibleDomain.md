## What changed

The item module proves ordinaryDirect_existsUnique, ordinaryPull_existsUnique,
ordinaryOpen_existsUnique, gamma_evaluation, level_origin and gamma_isIso.
Existing signatures and all public imports stay unchanged. Private proved helpers
identify the intrinsic and constant-scalar encodings sectionwise and prove the
unit-normalized uniqueness of an adjunction mate through equivalences.
The geometry declarations are reordered so gamma_isIso uses the existing
level_origin and gamma_witness_evaluation declarations. The latter remains postponed;
its explicit normalization equation suffices to prove levelwise invertibility,
followed by joint detection. No new theorem with sorry is introduced.

The node proof records these actual arguments. Ordinary comparisons use the existing
fixedDirect and equivalence-edge mate lemmas in FiniteConstantCoefficientTransport.
The origin argument uses the existing fixedDerivedOrigin proof and transports
intrinsic constructibility through the explicitly constructed encoding isomorphism.

## Proved and sorry left

Six of twelve original holes closed, all in
AlgebraicGeometry.ProEtale.SystemRefinement:
ordinaryDirect_existsUnique, ordinaryPull_existsUnique, ordinaryOpen_existsUnique,
gamma_evaluation, level_origin, gamma_isIso.
No holes added and no statements split off. The proof of gamma_isIso uses the
pre-existing gamma_witness_evaluation hole, as authorized by the stage-3 dependency rule.

Six original holes remain, all attached to
lem-pur-system-refinement-constructible-domain:
restrictionDirect_existsUnique, restrictionPull_existsUnique,
scalarPull_existsUnique, gamma_witness_evaluation, theta_evaluation,
normalized_operations. Their signatures and complete source/proof docstrings stay unchanged.

## No longer needed

The proof of gamma_isIso does not use the separate
lem-pur-system-proper-open-invertibility / Sheaf.Paper.SystemProperOpenInvertibility:
the already stated witness-evaluation equation proves invertibility of the evaluated
arrow, and semilinear joint detection finishes. This dependency is removed from
the node proof plan. The node remains available for its other users.
Removed unused private imports:
Sheaf.AlgebraicGeometry.StrictTowerProperOpenCalculus,
Sheaf.AlgebraicGeometry.ProperOpenInterchangeCoherence,
Sheaf.AlgebraicGeometry.ProperOpenComparisonSiteNormalization,
Mathlib.AlgebraicGeometry.Noetherian,
Sheaf.Paper.PullbackTorAmplitude,
Sheaf.Paper.FiniteCoefficientTensorCtf,
Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition.
Also removed the unused trial import Sheaf.Paper.ProEtaleLisseFiniteModelsFromLisse.
The strict-tower and interchange modules remain reachable through existing public
prerequisites. Site normalization, Tor preservation and direct-image composition
remain in the DAG's plan for the existing postponed clauses; their imports should
be added when those proofs actually use them. They are not claimed globally pruned.

No module is withdrawn. All unit steps and target signatures are retained.

The ordinary comparison proof uses the existing
def-cbc-finite-constant-coefficient-transport as an auxiliary tool, specifically its
proved fixedDirect and equivalence-edge mate facts; this supplies the canonical
scalar identifications required by the node. No tool_uses approval was added by
the worker. The independent reviewer should record any required approval.

## Where the brief, the DAG or earlier work was wrong

The existing scalar restriction and intrinsic restriction have different definitions;
they must be identified by a constructed identity-on-sections natural isomorphism,
including the sheafification-unit equation for the scalar action. Definitional
identification alone does not suffice. The ordinary left comparisons are obtained
by invertible mates through equivalences with their explicit unit equations.
No statement is disputed or changed.

## Second reading by C7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
