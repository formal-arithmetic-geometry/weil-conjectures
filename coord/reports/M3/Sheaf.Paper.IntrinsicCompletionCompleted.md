## What changed

Prove the two remaining holes in Sheaf.Paper.IntrinsicCompletionCompleted without changing
any existing declaration signature or definition. The first proof checks that the exterior
transition fixes the degree-zero unit, then checks the total-tensor summand and product
identities. The descent proof constructs the complex fiber functor and its natural unit,
proves that it preserves quasi-isomorphisms using K-flat Koszul factors, exact countable
products and mapping-cone triangles, and applies localization to the functor and unit.
All additional helpers are private and proved; there are no new split statements.
The tensor-unit and tensor-map calculations are first proved for an abstract additive
monoidal category and then applied to the sheaf category. This avoids repeated conversion
of the concrete sheaf tensor construction. No existing definition or signature changes.
The localization calculation is also proved for an abstract abelian category before
specialization. Explicit quasi-isomorphism lemmas for localization and shifts avoid
repeated inference through the concrete tensor construction. Profiling options are
absent from the delivery file; the required delivery compile checks that file.

Retain the existing constant-realization theorem rather than restating its K-flat clause.
Update the item's existing DAG proof fields to record the realized argument.
Only the assigned module, its node and the scoped-proof-context change record are
delivered; no other module is adapted. The preflight scanner flags section variables
and section-local transparency settings as a command/interface change. The record
coord/changes/M3-intrinsic-completion-scoped-proof-context.md lists the original and
new commands and checks the unchanged consumer interfaces. No existing public
signature, definition body, visibility or instance attribute changes.

## Proved and sorry left

Closed 2 of the 2 holes remaining in the current source:
AlgebraicGeometry.Scheme.completedKoszulLift_relation and
AlgebraicGeometry.Scheme.completedIntrinsicCompletion_descends
(node def-weil-pbc-intrinsic-completion). No sorry remains in the item, and no hole is added.
The five holes already closed by M5 stay proved.

The proof uses existing named K-flat interfaces, including the still-stated
constantRealizationDerivedScalarExtension and adicDatumExtension_kflat; proving those
interfaces belongs to their items. There is no claim to have closed those dependency holes.

Both original statements and all existing definitions remain unchanged.
Validation is repeated against the current shared sources by the delivery tool.

## No longer needed

Remove the direct proof import Sheaf.CategoryTheory.Triangulated.DerivedLimitProducts.
The proof uses HomologicalComplex.quasiIso_limMap from the source-library TowerLimit
module instead. No quotient-tower comparison or chosen K-flat representative is needed.
The existing DAG had no proof dependencies to withdraw. No whole library module is
claimed unreachable, and the unit's realized statement and proof steps are preserved.


## Where the brief, the DAG or earlier work was wrong

The retained sandbox included an old copy of the coefficient-adjunction module with
a pre-existing sorry and an unused proof import removed. The shared source now proves
that theorem and has already removed that import. Dropping the obsolete sandbox copy
and its change record avoids reverting the shared proof; no consumer adaptation is needed.
The first dry run identified this stale copy as an added hole. No new hole is introduced.
No existing statement is disputed or weakened.

Edge cases: the argument never requires a positive number of generators, a nonzero ring,
or a nonempty scheme. Exterior-power degree zero uses its canonical equivalence with A;
extension to positive cochain degrees uses zero objects. The product and localization
arguments apply equally to zero complexes and the empty tuple.


The resumed item compile completed cleanly in 15.8 seconds. The earlier delivery
probe also compiled; its style warning was removed by replacing the proof-local
`letI` with `let`. The final dry run is repeated with the change record required by
preflight for scoped proof commands.

## Second reading by M3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
