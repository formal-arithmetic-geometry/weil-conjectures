## What changed

Proved `AlgebraicGeometry.ProEtale.exists_etale_cech_cocycle_lift` with its original
signature and public imports. The proof uses a common affine étale covering
presentation, the canonical coefficient section colimits, finite representatives
and eventual zero, and a categorical/ordered Čech complex isomorphism after ULift.

Added six modules, all proved or concretely constructed:

- `AffineComparisonEtaleCechSystem`: the geometric system and its nerve cones.
- `CechNervePresentationConstruction`: wide-pullback maps, face equations, and
  scheme limit cones for every repeated intersection.
- `AffineComparisonEtaleCoverPresentation`: finite-family presentations, proved
  using the existing affine disjoint-union factorization, single-surjection
  presentation, and finite affine open-cover descent.
- `AffineComparisonEtaleCechPresentation`: combines the geometric constructions.
- `AffineComparisonCechSystemSections`: constructs the stage complex maps and
  proves that every finite Čech cocycle lifts to a stage cocycle.
- `OrderedCechUliftComparison`: constructs the required complex isomorphism.

Updated the item's proof route in its DAG node. No existing signature or data
construction was changed, and no forced adaptation is needed. The fetched base
requires a restoration record for the originally assigned, now absent module;
see `coord/changes/restore-affine-comparison-cech-cocycle-descent.md`.

## Proved and sorry left

Closed the hole from the initially assigned snapshot in
`AlgebraicGeometry.ProEtale.exists_etale_cech_cocycle_lift`: **1 of 1**.
Added **0 holes**. There are **no remaining `sorry` declarations** in any delivered
module. This is a proof, rather than a decomposition into further obligations.

The auxiliary results proved include
`exists_affine_etale_cover_presentation`, `exists_affine_etale_cech_system`,
`AffineEtaleCechSystem.exists_cocycle_lift`, `presentedNerveIsLimit`, and
`Presheaf.orderedCechUliftIso`. All geometric and complex-map data are explicit
constructions. The only witnesses extracted by the top-level proof occur inside
a theorem proving an existential proposition.

All seven files compile in import order. An explicit `#print axioms` for the
original theorem returned exactly `propext`, `Classical.choice`, and `Quot.sound`.
The required dry run checks every
file and probes the axioms of its declarations. Empty indexing, repeated indices,
empty schemes, and the zero sheaf require no extra hypothesis: the finite-family
factorization, finite open-cover descent, wide-pullback construction, and finite
coordinate arguments include these cases.

## No longer needed

Removed these seven proof imports from the item's route; their statement modules
are not imported anywhere in this delivery:

- `Sheaf.AlgebraicGeometry.AffineEtaleSiteColimitStatement`
  (`lem-weil-pbc-affine-etale-site-colimit`).
- `Sheaf.AlgebraicGeometry.FibreProductLimit` (`lem-kun-fibre-product-limits`).
- `Sheaf.AlgebraicGeometry.LimitAffineTransition`
  (`lem-weil-pbc-limit-affine-transition`).
- `Sheaf.RingTheory.IndEtaleStability` (`lem-weil-pbc-ind-etale-stability`).
- `Sheaf.CategoryTheory.ExistsDirectedReindexing`
  (`lem-weil-pbc-filtered-category-directed-cofinal`).
- `Sheaf.AlgebraicGeometry.EtaleCohomologyLimitOfSchemes`
  (`lem-weil-pbc-etale-cohomology-limit-of-schemes`).
- `Sheaf.AlgebraicGeometry.ProEtaleComparisonPullbackSections`
  (`lem-cbc-comparison-pullback-sections`).

The previous route also no longer needs separate proof dependencies on
`def-weil-pbc-ind-etale-algebra`, `lem-weil-pbc-affine-scheme-qcqs`,
`def-weil-pbc-sites-and-cohomology`,
`lem-weil-pbc-etale-composition-cancellation`,
`lem-weil-pbc-etale-base-change-finite-limits`, or
`lem-weil-pbc-etale-base-change-continuous`. Their required mathematical facts
are supplied by the existing source-library or Mathlib APIs, without those
statement modules. This is pruning from this proof route; other parents may
still use these nodes.

The item's direct proof imports of the source-library modules
`WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine` and
`WeilConjectures.SixFunctors.ProEtale.Comparison.Continuity` moved to the geometric
and coefficient helper modules respectively. They remain used transitively and
are **not** claimed as pruned modules. The statement's original public imports
are preserved. The second reading also removed redundant helper imports already
publicly supplied by their retained dependencies.

## Where the brief, the DAG or earlier work was wrong

The original two consecutive Čech descent reductions can be combined into one
simultaneous geometric covering presentation followed by one finite-coordinate
section-colimit argument. It is unnecessary to develop the proposed general
site-colimit and higher étale cohomology continuity statements for this item.
The already proved source-library affine-surjection presentation and finite
open-cover descent results suffice. No mathematical statement was disputed. The second reading corrected the
continuity citation: Tag 099S proves continuity and Tag 099T identifies the unit.

During the session the read-only shared checkout was refreshed and the assigned
module and node disappeared from that working snapshot, together with their
parent's import. This sandbox preserves the exact originally assigned signature
and node statement; its updated proof route is based on the initial assignment.
No shared source was edited. The required delivery tool selects the fetched
base and checks the resulting delivery.

## New nodes

`lem-cbc-affine-comparison-cech-cocycle-descent` restores the originally assigned
node, which the fetched delivery base no longer contains. Its statement and
signature are unchanged; its proof route is now completely implemented. The
restoration record is
`coord/changes/restore-affine-comparison-cech-cocycle-descent.md`.

`def-cbc-affine-etale-cech-system` records the concrete geometric system data and
its diagram/cone constructions in `AffineComparisonEtaleCechSystem`.

`lem-cbc-cech-nerve-presentation-construction` records `presentedNerveIsLimit` and
the concrete wide-pullback transition and face constructions in
`CechNervePresentationConstruction`.

`lem-cbc-affine-etale-cover-presentation` records the proved finite-family
presentation theorem in `AffineComparisonEtaleCoverPresentation`; nothing is
left for another worker in this geometric reduction.

`lem-cbc-affine-etale-cech-presentation` records the proved assembly into an
`AffineEtaleCechSystem` with limiting nerve cones.

`lem-cbc-affine-cech-system-cocycle-lift` records the proved finite-coordinate
representative and eventual-zero argument in `AffineComparisonCechSystemSections`.

`lem-cbc-ordered-cech-ulift-comparison` records the constructed complex isomorphism
in `OrderedCechUliftComparison`.

The restoration record above is required because the fetched base treats the
assigned item as new. Existing signatures, definitions and public imports are
unchanged. No forced adaptations were made.


## Second reading by E2

1. **Interfaces — pass, with the restoration limitation recorded.** I read all
   seven delivered modules and compared their paths against the current shared
   checkout: all seven are absent, so no current shared declaration is overwritten.
   A direct byte comparison confirms that `exists_etale_cech_cocycle_lift` has
   exactly the signature in both the restoration record's Old section and the
   assigned node's `lean.statement`. The initial checkout is no longer available
   for an independent historical diff; the delivery is therefore explicitly a
   restoration, not an unrecorded signature change. No definition, target,
   importer, or module held by another group is adapted.

2. **Proof and constructions — pass.** I read the wide-pullback maps and their
   projection identities, the test-cone construction of `presentedNerveIsLimit`,
   the disjoint-union/single-surjection presentation and finite-open-cover descent,
   the coefficient-unit naturality equations, both finite-coordinate arguments,
   and the ULift additive equivalence and chain-map equation. None constructs
   data from an unproved arbitrary existence theorem. The `Nonempty.some` uses
   in definitions select limit/colimit universal properties; all are proved here
   or upstream and their data are uniquely determined by those properties.
   The existential covering presentations and cochain representatives are
   eliminated only inside theorem proofs. There are no `sorry`, added axioms,
   unsafe declarations, opaque declarations, foreign implementations, or skipped
   kernel checks in the delivered sources. All seven files compiled without errors or warnings. A separate scratch copy
   with `#print axioms AlgebraicGeometry.ProEtale.exists_etale_cech_cocycle_lift`
   independently returned exactly `propext`, `Classical.choice`, and `Quot.sound`.
   The delivery tool additionally probes every declaration before pushing.

3. **Auxiliary statements and small cases — pass.** There are no split-off holes.
   The geometric presentation has no coefficient or cocycle conclusion, the
   sections result assumes the geometric system and proves a stage lift, and
   the ULift result is a purely categorical complex isomorphism. Each is a
   strictly smaller, fully proved part of the argument. For `n = 0`, the original
   covering forces an empty base; the finite disjoint-union and descended empty
   open cover give empty covering stages. The tuple sets in both coordinate
   arguments are then empty; filteredness still provides a stage and transition.
   For `n = 1` and repeated indices the wide-pullback projections retain all
   repeated factors, so no distinct-index hypothesis is hidden. The section
   argument also works in degree zero, for empty schemes and for the zero sheaf.
   Independent LeanFinder, Loogle and grep searches used different queries about
   filtered cocycle representatives and categorical complex identifications.
   Loogle found the same `Concrete.isColimit_exists_rep` API already used here.
   Source searches found no assembled replacement; the existing topological
   comparison concerns opens and module presheaves, and the étale-limit Čech
   colimit theorem concerns a directed scheme system with varying coefficients.

4. **Route and pruning — pass, with no target-closure progress claimed.** I read
   Stacks Tags 099U (condition (3)), 099S (continuity), 099T (the unit), and 01ZM,
   as well as the used upstream singleton-surjection, affine factorization and
   section-continuity declarations. The proof realizes the two finite Čech limit
   reductions simultaneously and never invokes injectivity or a primitive.
   The unit `sk-prop-sf-comparison` has empty `realized.statement` and
   `realized.steps`; no recorded unit realization is replaced. The current
   parent `AffineComparisonInjectiveVanishingAux` no longer imports this item,
   and the current ancestor has also been revised. Thus the seven old proof
   dependencies listed above describe pruning relative to the assigned route;
   this restoration itself does not remove any current shared module or establish
   a net reduction in the targets' current import closure. I removed redundant
   helper imports of `Grp.FilteredColimits`, `Over.Products`, the ordered Čech
   module and the categorical Čech module where retained public imports already
   supply them. The public AB import is needed by signatures using
   `comparisonUpperStar` with its Grothendieck-abelian coefficient instance.

5. **DAG — pass after metadata repair.** I matched every node's declaration and
   verbatim Lean signature with its module. In every node `proof_deps` equals
   the union of its proof-step `uses`. The item's three steps match the geometric
   system, finite-coordinate lift and ULift transport in its Lean proof; the
   supporting nodes describe the actual universal-property and continuity APIs.
   All seven records include their source, chapter, unit, creation metadata,
   searches, blueprint provenance and Lean record. I removed `reviewed` and
   `reviewed_proof` stamps copied from D3's earlier landing: they are historical
   metadata, not a review of this restored E2 proof. That history remains in the
   restoration record. I corrected the section node's continuity citation to
   include Tag 099S.

**Changes made by this reading:** corrected the continuity source citations,
removed four redundant import lines, removed the two stale review stamps, and
clarified the historical signature comparison and pruning/closure limitation.
No proof body, statement, or data construction needed repair. One assigned hole
is closed, zero holes are added, and zero holes remain in the delivered modules.


Validation after the second reading: the required `deliver3.py E2
Sheaf.AlgebraicGeometry.AffineComparisonCechCocycleDescent --no-push` printed
`OK (dry run)` at commit `0b798f3070`: all final files compiled, the per-declaration
axiom probes reported no additional axiom, and preflight passed. Review class is
CODEX because this is a restoration with six supporting modules, new nodes and
a change record. The delivery command repeats these checks before pushing.
