## What changed

Proved AlgebraicGeometry.Etale.isIso_strictHenselizationCohomologyComparison by
combining the four factors of its existing definition. The middle factor uses
AlgebraicGeometry.Etale.isIso_strictHenselization_baseChange_globalHomology on F[0];
Mathlib supplies the other factors' isomorphism instances and their composition.

Three private helpers in the assigned module avoid expensive projection normalization:
mappedMate is a transparent generic construction; map_mate_eq_mappedMate proves the
raw map equals that construction by reflexivity on abstract categorical data;
isIso_globalHomology_of_data transports the square before projecting its mate.
Every helper is fully proved. All existing signatures, definitions, visibility and
imports remain unchanged. The node records this proof-local implementation of its plan.

The inherited attempt edited StrictHenselizationRestriction, held by Z2. That edit,
its node copy and its change record have been removed from the delivery. The proof
compiles against the original dependency, in about 38 seconds. No push or global
build was run.

## Proved and sorry left

Closed 1 of 1 original holes:
AlgebraicGeometry.Etale.isIso_strictHenselizationCohomologyComparison
(node lem-weil-pbc-unrestricted-strict-henselization-stalk-comparison).

No sorry remains in the delivered module. No holes were added or split off.
This is a proof from the existing lower declarations, not a claim that every
transitive dependency is free of sorry.

## No longer needed

None. Both original imports and both planned dependency nodes remain needed.
No unit statement or realized unit step is bypassed; sk-thm-br has no realized
statement or steps attached to this auxiliary node. No proof import was added.

## Where the brief, the DAG or earlier work was wrong

The mathematical four-factor plan is correct. Direct application of the existing
middle-factor theorem causes expensive kernel normalization of projected derived
mates. A private generic equality allows explicit transport instead.

The inherited dependency edit was not allowed by the forced-adaptation rules:
the dry run reported that StrictHenselizationRestriction compiles unchanged
against the changed dependencies. The current proof fixes that issue entirely
within the assigned module and leaves Z2's module untouched.

## Second reading by G2

1. The delivered module preserves the theorem signature and both existing imports byte for byte;
the proof unfolds the unchanged four-factor definition and closes the target without `sorry`.
The local module compile succeeds.
2. The private helpers are fully proved: `mappedMate` is a transparent definition,
`map_mate_eq_mappedMate` is reflexivity, and `isIso_globalHomology_of_data` reduces by equality
induction to the imported strict-local base-change theorem. No new public statement or hollow
definition was added.
3. The existing DAG node's statement is unchanged semantically; only its proof route and origin
fields record the actual proof. Its two declared proof dependencies remain exactly the imports used.
4. No import or proof dependency can be pruned: restriction supplies the comparison definition and
the base-change module supplies the middle-factor theorem. The four-factor route is retained.
5. The unit `sk-thm-br` has no realized statement or steps attached to this auxiliary node, so its
route is unaffected. I removed no declarations, made no forced adaptations, and found no shorter
existing theorem that closes the target.

Changed after this reading: added this review record only; no Lean code, signatures, definitions,
imports, or DAG statements were altered.
