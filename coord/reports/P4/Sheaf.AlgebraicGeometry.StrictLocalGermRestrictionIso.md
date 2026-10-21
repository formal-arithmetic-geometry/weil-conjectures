## What changed

Retire the already proved duplicate Sheaf.AlgebraicGeometry.StrictLocalGermRestrictionIso,
as assigned in coord/retire-items.tsv. Redirect its node
lem-weil-pbc-strict-local-germ-restriction-iso to the unchanged adopted theorem in
WeilConjectures.AlgebraicGeometry.StrictLocalGermRestrictionIso.

Prove the model-independent theorem
AlgebraicGeometry.Etale.PointedEtaleSectionCone.isIso_restriction in the new module
Sheaf.AlgebraicGeometry.PointedEtaleSectionConeStalkIso. It applies to arbitrary schemes,
a compatible pointed section cone, and a compatible geometric lift whenever the specified
identity-neighbourhood germ of the pulled-back sheaf is invertible. Its proof combines the
inverse-image stalk/germ comparison with colimit uniqueness and cancellation.

Adapt the two live callers, Sheaf.AlgebraicGeometry.StrictLocalCohomologyGerms and
Sheaf.AlgebraicGeometry.StrictLocalConstantComparison, to this general criterion. Their
closed lift is supplied by strictHenselizationResidue, its closedness follows from the
residue prime-comap formula, and its terminal germ is invertible by the existing strictly
henselian sections/stalk theorem. Their small-colimit scheme model, restriction r, all
signatures and all resulting maps are preserved. The public source-isomorphism definition
changes only its proof of IsIso r. The change record is
coord/changes/P4-retire-strict-local-germ-restriction-iso.md.

The general criterion and both adapted consumers compile without warnings. A temporary
Lean probe proves by rfl that strictLocalCohomologySourceIso equals its original definition.
The new theorem and source isomorphism use only propext, Classical.choice and Quot.sound.
All five direct importers of the adapted consumers compile: LocallyConstantTorsionLocalAcyclicity,
StrictLocalMateProjectionData, StrictLocalMateContinuityPresentation,
StrictLocalSmallModel.DerivedCohomologyGermIso and
StrictLocalSmallModel.StrictLocalCohomologySourceColimit. No adopted source module is edited.

## Proved and sorry left

The assigned item has zero holes before and after retirement: 0 closed, 0 added, 0 split
off. Its existing theorem was already proved. The new general theorem
AlgebraicGeometry.Etale.PointedEtaleSectionCone.isIso_restriction is fully proved. The adapted declarations AlgebraicGeometry.Etale.strictLocalCohomologySourceIso and
AlgebraicGeometry.Etale.exists_strictLocalConstantComparison remain sorry-free. No theorem is handed off and no definition contains
a hole or obtains arbitrary data from an unproved existence theorem.

## No longer needed

Withdraw lean/Sheaf/AlgebraicGeometry/StrictLocalGermRestrictionIso.lean and its duplicate
specialized declaration. Its two live imports are replaced by the general criterion plus
explicit proof imports of Sheaf.Paper.StrictHenselizationFunctoriality and
WeilConjectures.AlgebraicGeometry.StrictlyHenselianSectionsStalk. The original public
StrictLocalSectionCone dependency is already imported directly by
StrictLocalCohomologyGerms and through LocalAcyclicityAbelianSheaf by the constant comparison.

The withdrawn module's explicit proof imports of InverseImageStalkGerm,
EtaleLocalRingTriples, StrictHenselizationExtension and StrictHenselizationTriples no longer
belong to a specialized SHEAF theorem. InverseImageStalkGerm is the sole private proof
import of the new general criterion. The others remain where the actual ring/residue
construction or the adopted proof uses them; this delivery does not claim those modules
are globally unused. No DAG node is deleted. The canonical strict-local theorem and all
parents retain their mathematical statements and unit route; only its Lean realization
is redirected. The two adapted consumer proof plans record their direct general route. This criterion is
a general tool below the unit route; no unit statement or step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The generic brief describes proving a hole, but the queue assigns retirement of a
zero-hole duplicate. A rebase or a compiling no-op would not perform that repair.
The adopted theorem cannot directly replace the small-colimit theorem in the live
consumers: their scheme and structural-map expressions are different models. The new
general criterion avoids changing those definitions. Its point compatibility concerns
the actual geometric lifts, not merely the underlying topological closed point.

The four additional direct importers listed in the older retirement inventory are
quarantined: LocalAcyclicityClosedFibreOrdinaryGerm, StrictHenselizationStalkFormula,
StrictLocalBaseChangeGlobalHomology and UnrestrictedStrictHenselizationStalk. Their
archives, Lean attachments and DAG dependencies are preserved. They already depend on
the separately retired specialized restriction API and need their own rework; this packet
does not delete an absent path, discard an archived proof, or pretend they are unused.
The canonical DAG node they cite still has its complete adopted realization.

Initial compiles found unpublished PointedEtaleSectionCone/StrictLocalSectionCone artifacts.
They became available during the session, and subsequent compiles succeeded normally.

An additional full compile of StrictLocalSmallModel.StrictLocalLocalizedHomGerm timed out
at 60 seconds. The unchanged file also timed out against the published baseline in a
separate sandbox without our compiled overlay, so this is a pre-existing compile limit
issue. It is not counted among the five successful direct-importer checks. Its affected
sourceLeg_eq_sectionRestriction calculation compiled in 15 seconds in a separate temporary
diagnostic probe using the changed definition. The packet does not split or alter that
module or claim its full compile passed.

## New nodes

lem-weil-pbc-pointed-section-cone-stalk-iso is the general pointed-cone criterion in
Sheaf.AlgebraicGeometry.PointedEtaleSectionConeStalkIso. It is fully proved from the existing
inverse-image stalk/germ comparison and the cone's restriction universal property. It has
no strict-local ring or scheme assumption and does not define or choose a new map.
Edge cases: the zero sheaf and identity morphism satisfy the same argument; arbitrary
initial diagrams and arbitrary compatible y are allowed; no torsion, properness, finiteness
or nonempty-fibre restriction is introduced. Invertibility of the actual identity germ is
explicit, so the assertion makes no unjustified claim for general T. Real searches through
Lean Finder, Loogle, LeanSearch and grep are recorded in the new node. Blueprint searches
for pointed section cone and germ restriction found no existing matching node.

## Second reading by P4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
