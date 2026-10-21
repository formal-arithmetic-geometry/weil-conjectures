## What changed

Restored Sheaf.Paper.ResidueLissePerfectLift from the quarantine path recorded in
coord/rework.tsv. Every public signature and definition is unchanged from the archive.
Added explicit private imports of Sheaf.Paper.FinitePerfectQuotientModels and
Sheaf.Paper.KoszulReconstruction. Removed the unused private finite-level comparison
import. The existing complete argument constructs normalized coefficient comparisons,
uses uniform finite quotient models and adic realization, and composes the actual
completion-unit isomorphism with exact slice restriction.

Adapted the unclaimed Sheaf.Paper.FinitePerfectQuotientModels: retain its live public
interface verbatim and restore the archived residuePerfect_quotient_models_succ and
residuePerfect_finite_quotient_models, together with their proved private restriction
helpers. This repairs the missing declared dependency required by the restored item.
Change record: coord/changes/D4-restore-residue-finite-quotient-induction.md.

Completed AlgebraicGeometry.Scheme.completedAdicScalar_exists in the unclaimed
Sheaf.Paper.CompletedAdicIntrinsicCompletion. Construct the compatible cone of
constant residue maps, use the coefficient limit, and extend by sheafification;
uniqueness follows by testing all projections and constant sections. No statement,
definition or import of this module changes. Change record:
coord/changes/D4-completed-adic-scalar-universal-property.md.

## Proved and sorry left

The assigned archive has zero textual holes, and the restored assigned module has
zero holes. No assigned hole was newly closed (0 of 0), and no new split was made.
AlgebraicGeometry.Scheme.residue_lisse_perfect_lift and all its helpers compile with
complete proof bodies against the recorded dependencies.

The adapted dependency restores one archived named hole:
AlgebraicGeometry.Scheme.residuePerfect_quotient_models_succ,
node lem-weil-pbc-residue-perfect-finite-quotient-models. Its signature, source and
complete proof in words are the archived ones; it is an existing DAG obligation,
not a new lemma or a renamed copy of the item. The restored aggregate theorem
AlgebraicGeometry.Scheme.residuePerfect_finite_quotient_models is completely proved
from that successor result by induction. No other sorry is added. This restores a required existing dependency;
it is not a decomposition of an assigned hole.

Closed the existing hole AlgebraicGeometry.Scheme.completedAdicScalar_exists
(node def-weil-pbc-intrinsic-completion) without adding any lower hole. The other
four existing holes in that adapted module remain unchanged, all under the same
node:

- AlgebraicGeometry.Scheme.completedAdicKoszulUnitZero_exists
- AlgebraicGeometry.Scheme.completedAdicKoszulTensorUnitF_comm
- AlgebraicGeometry.Scheme.completedAdicKoszulUnitF_comm
- AlgebraicGeometry.Scheme.completedAdicIntrinsicCompletion_comparison

Across the three delivered modules: one existing hole closed, one archived hole
restored, five holes left, net zero change to the current source's hole count.
The assigned item itself remains zero of zero; no new nodes or splits.

The pre-existing dependency
AlgebraicGeometry.Scheme.finitePerfectModels_adic_realization also remains sorry in
the unchanged library. No definition contains a hole. No axiom was introduced.

Remote lcompile.py --all compiled all three delivered modules cleanly:
CompletedAdicIntrinsicCompletion (10.8 s), FinitePerfectQuotientModels (9.8 s),
and ResidueLissePerfectLift (12.2 s).

## No longer needed

Removed the assigned module's private import
Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonFiniteLevel. The coefficient scalar
map's local bijectivity instances are already supplied by ProEtaleFiniteModules.
The assigned DAG proof_deps and all four steps remain the actual argument; none of
those nodes or modules is pruned. In particular the quarantined item and the
finite-quotient induction are needed despite their absence from the current Lean
import graph. No module or DAG node is withdrawn.

The dependency restoration does not restore the archive's unused proof imports
FiniteRingConstructibleDerivedOrigin, FiniteRingDerivedLocalConstancy,
NilpotentReductionLissity, ConnectedEtalePerfectConstant,
FiniteTypeLocallyConstantSerre, SiteDerivedTensorDescentIndependentCoefficients,
ConstantEtaleSheafShortExact, or RingedTopoiCanonicalTensorPullbackOfUniverses:
these belong to the pending successor proof and are not used by its present body.
Their DAG dependencies remain recorded for that proof obligation.

## Where the brief, the DAG or earlier work was wrong

The item is a zero-hole quarantine restoration, rather than an unproved theorem.
Its source must be read from quarantine/Sheaf/Paper/ResidueLissePerfectLift.lean.
The current DAG attachment for its finite-quotient dependency lists two theorems
missing from the source because W6 treated absent quarantined consumers as unused.
B3 restored the interface but deliberately omitted that successor theorem and its
proved aggregate consumer. Restoring this assigned parent requires them, and they
are restored under the existing attachment without changing their statements.

The shorter-route search used LeanFinder, Loogle and source ripgrep. LeanFinder
returned unrelated period-ring and etale-algebra constructions; Loogle returned no
Sheaf/IsAdicComplete match. Source search found no substitute for the recorded
finite-quotient and reconstruction argument. The unit's route is preserved.

## Second reading by D4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
