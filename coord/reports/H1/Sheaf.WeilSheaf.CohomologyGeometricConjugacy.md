## What changed

Withdraw the duplicate modules Sheaf.WeilSheaf.CohomologyGeometricConjugacy and
Sheaf.WeilSheaf.CohomologyGeometricEquivalence. Their existing DAG nodes now attach to
WeilConjectures.WeilSheaf.CohomologyGeometricConjugacy and
WeilConjectures.WeilSheaf.CohomologyGeometricEquivalence, respectively.
The existing upstream theorem has the exact assigned signature and a complete proof.
The upstream definition implements the canonical derived-global-section transport.
The declaration names, hypotheses, universes, and conclusions are retained.

On resuming the interrupted session, the shared tree already imports the upstream
conjugacy module in WeilConjectures.WeilSheaf.PoincareDuality. There are now no external
consumers of either Sheaf duplicate, so no consumer adaptation is delivered.
The earlier exploratory proof copies are excluded from the delivery.
Change record: coord/changes/H1-geometric-cohomology-upstream-reuse.md.

## Proved and sorry left

Resolved by existing upstream proof, 1 of 1 original direct holes:
AlgebraicGeometry.WeilSheaf.cohomologyLinearEquivOfGeometricFiberIso_map_frobenius
(node lem-pod-cohomology-geometric-conjugacy).
The source proof inverts geometric conjugacy, applies derived transport and homology,
and conjugates by the specified carrier comparisons. Its power helper proves r=0 by
identity transport and the successor by composition.

Added holes: 0. Split off: 0. Sorry left in delivered Lean modules: 0.
The withdrawn equivalence definition had 0 holes. Both withdrawn modules become empty
module files. Existing transitive upstream dependencies still contain sorryAx; this
is reuse of an existing proof, not a claim of a completely axiom-free dependency closure.

## No longer needed

Withdrawn modules:
- Sheaf.WeilSheaf.CohomologyGeometricConjugacy
- Sheaf.WeilSheaf.CohomologyGeometricEquivalence

Imports removed with the withdrawn modules:
- Sheaf.WeilSheaf.CohomologyGeometricEquivalence
- Sheaf.Paper.CommonStageCompactWeilCohomology
- Sheaf.Paper.ConstantWeilStructure
- Sheaf.Paper.PointProEtaleSectionsExact
- Sheaf.SixFunctors.FrobeniusCohomologyTransport
- Sheaf.Paper.GlobalGeometricFrobenius
- WeilConjectures.WeilSheaf.CohomologyExact

The five Paper/SixFunctors imports have nodes def-weil-ordinary-compact-cohomology,
def-weil-constant-weil-structure, lem-weil-point-proetale-sections-exact,
def-weil-frobenius-cohomology-transport, and def-weil-global-geometric-frobenius.
Those modules are unnecessary for this proof: its statement uses the source library's
WeilSheaf encoding, whose derived transport and exactness APIs are already available.
They may still be needed elsewhere. CohomologyExact remains imported by the retained
upstream equivalence. Both geometric equivalence/conjugacy nodes remain attached to
the source declarations. No unit statement or proof step is bypassed: this reuses
the same geometric transport argument in item (6) of Poincare duality.

## Where the brief, the DAG or earlier work was wrong

The plan missed the exact existing upstream theorem and its canonical equivalence,
which have the same fully qualified names as the Sheaf duplicates. Importing both
implementations would create duplicate declarations. Retiring the unused duplicates
and repointing their DAG attachments follows the one-definition-per-notion rule.

The old equivalence composes the derived forgetful comparison, exact sections/homology
comparison, and derived-composition comparison. The upstream construction combines
these canonical comparisons and exposes compatibility lemmas needed for its conjugacy
proof. This is recorded as a consolidation of the definition implementation for
independent review, rather than a claim that the old and new terms are definitionally
equal. No target statement refers to this equivalence in its signature.

## Second reading by H1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
