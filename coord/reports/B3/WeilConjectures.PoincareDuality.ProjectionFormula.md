## What changed

In WeilConjectures.PoincareDuality.ProjectionFormula, prove boundedConstructibleExceptionalProjectionMorphism_natural_right by the faithful inclusion and the existing ambient naturality statement. Repair the existing compile timeout using two local monoidal instance aliases and local irreducibility settings. Every existing definition body, declaration attribute, signature and visibility is unchanged. No imports changed and no other modules adapted. The change record is coord/changes/B3-projection-formula-local-elaboration.md.

## Proved and sorry left

Closed 1 of the original 5 holes: AlgebraicGeometry.ProEtale.CondensedRing.boundedConstructibleExceptionalProjectionMorphism_natural_right. Added 0 holes and split off 0 statements. Full module compiled in 41.2 seconds.

Four original holes remain, all in AlgebraicGeometry.ProEtale.CondensedRing:
- isIso_openImmersionProjectionComparison: derived extension-by-zero projection formula.
- exceptionalProjectionMorphismOfCompactification_natural_right: naturality of the three-factor composite.
- boundedConstructibleExceptionalProjectionMorphism_natural_left: first-variable naturality of the same composite.
- isIso_boundedConstructibleExceptionalProjectionMorphism: derived compact-support projection formula.

These are unchanged statements, not new split-offs. No DAG node has a lean.module attachment to this source module, and the original file has no blueprint node tags. Their proof descriptions are in the existing module docstring. No new sorry appears in a definition.

## No longer needed

None. Both original public imports are needed by the existing definitions and statements. No dependency modules or unit steps are bypassed. No new imports were added.

## Where the brief, the DAG or earlier work was wrong

The assigned module has no matching DAG node, so there is no attached numbered DAG plan to update. The supplied source already times out; an earlier delivery was returned for the same 68-second compile failure. The local elaboration repair is therefore necessary even for a short naturality proof. An initial no_expose variant compiled but the stage-3 gate rejected its attribute changes; the delivered version removes those changes and also compiles within the limit. The mathematical construction is unchanged. The two isomorphism holes require derived sheaf theory, beyond the formal naturality calculation; this delivery does not claim to prove them. No new nodes or forced adaptations.

## Second reading by B3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
