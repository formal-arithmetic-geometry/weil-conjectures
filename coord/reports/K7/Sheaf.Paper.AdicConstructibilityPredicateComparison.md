## What changed

Proved `AlgebraicGeometry.ProEtale.adicConstructibilityPredicateComparison` in its original
module, with the statement unchanged. The proof uses the existing integral comparison,
finite-field local freeness, and bounded-image algebraic-closure local freeness. It reuses
proved private transport and stratification helpers through private `import all` imports.

The integral branch explicitly identifies the spectral-norm integers of the universe lift
with the embedded integers by an isometric ring isomorphism. The finite-field branch
identifies continuous coefficients of `ULift E` with those of E and pulls back finite free
modules from the point. Finite free scalar modules have the zero-matrix presentation.
Both module predicates are transported across coefficient isomorphisms. The derived
assertion is pointwise substitution in cohomology, preserving boundedness.

The existing public imports are retained. No definition, public signature, or consumer is
changed. The node proof is updated to describe the argument and its actual dependencies.

## Proved and sorry left

Closed the single hole in
`AlgebraicGeometry.ProEtale.adicConstructibilityPredicateComparison`
(node `lem-sfb-adic-constructibility-predicate-comparison`).
Holes closed: 1. Holes added: 0. Holes left in the delivered module: 0.
No statements were split off. Remote single-file compilation passed cleanly in 9.0 seconds after the preflight repair.

## No longer needed

Removed the private proof import `Sheaf.AlgebraicGeometry.FiniteConstantLocalModel`.
Retained `Sheaf.Paper.CartesianCoefficients` because it is a protected unit-route import.
The proof uses the canonical coefficient
isomorphisms already present in the module pullback API, and the proved reverse-implication
helper of `IntegralLfpConstantModelComparison`.

Direct proof dependencies no longer needed:
`def-weil-pbc-internal-abelian-sheaf-module-equivalence` and
`det-def-sfb-constructible-local-model`.
Removed the latter obsolete entry from the node’s top-level `tool_uses` approvals.
Both predicates already use the same internal-module category; the sectionwise equivalence
need not be applied. The Cartesian-coefficient module stays imported for the prescribed unit route.
Its
additional twist and finite-free assertions are not applied in this proof. The constant-model implication is already proved in
the integral comparison module. These dependencies may still be needed elsewhere;
no module is withdrawn and no upstream declaration is changed.

## Where the brief, the DAG or earlier work was wrong

The plan is mathematically sufficient, but its Lean interfaces require two coefficient
identifications: the integral comparison uses spectral-norm integers in the scheme
universe, whereas the certificate uses embedded integers of a Type-0 field; the finite-field
local-triviality theorem uses coefficients in the scheme universe. The proof supplies
these isomorphisms explicitly, including transport of both constructibility predicates.
The Noetherian subspace argument and reverse implication already exist as proved helpers
in the integral comparison module, so they are reused.

No target statement or unit route is changed. The sources used are the current blueprint
`sk-def-sfb-constructible/_section.md` and `det-existence-restriction.proof.md`, together with
the existing coefficient-specific node proofs. Empty schemes, empty strata, rank zero,
and torsion integral scalar modules retain their original generality.

The integral coefficient isomorphism is generalized from the proved private construction in
`IntegralConstantModelHeartClosure`: it accepts any embedded finite field certified by the
coefficient predicate and explicitly supplies its normed-algebra instance. No dependency
on the heart-closure theorem is introduced. Existing proved private helpers are used through
`import all`; none is restated with an unfinished proof.

Preflight initially required restoration of the protected Cartesian-coefficient import and
flagged an added namespace opening. Restored the import, qualified the two Limits names,
and restored the original `open CategoryTheory` command. No declaration interface change
or change record is needed.

## Second reading by K7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
