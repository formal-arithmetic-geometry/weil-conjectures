## What changed

Completed the DIFFERENT retirement repair for
Sheaf.AlgebraicGeometry.EtaleInjectiveSectionsComparison (coord/retire-items.tsv).
The assigned module already had zero sorry bodies. Withdraw its duplicate module
and adopt sectionsPullbackNat, termwiseSectionsCohomology,
termwiseSectionsRestriction, termwiseSectionsToDerived and
representativeSectionsComparison from the unchanged
WeilConjectures.AlgebraicGeometry.EtaleInjectiveSectionsComparison.
All five original construction blocks are byte-identical to the adopted source.

Preserve the mathematically distinct small-model comparison, with precisely its
old hypotheses, objects and maps, as
AlgebraicGeometry.Etale.smallModel_injectiveSections_strictLocal_comparison in
Sheaf.AlgebraicGeometry.StrictLocalSmallModel.EtaleInjectiveSectionsComparison.
Its first two conjuncts reuse the adopted theorem's identical stage and transition
conjuncts. Its last conjunct follows from sectionsComparison_triangle_naturality
on Q.smallModelLegs and Q.smallModelOver. This short proof also removes the duplicate
private etale-invertibility argument. There is no new mathematical obligation.

The two direct importers, StrictLocalSmallModel.StrictLocalInjectiveSourceComparison
and StrictLocalSmallModel.StrictLocalInjectiveSourceSections, now publicly import
the focused small-model module. The three proof callers,
StrictLocalSmallModel.StrictLocalInjectiveSourceDerivedRestriction,
StrictLocalSmallModel.StrictLocalInjectiveSourceRestriction, and
StrictLocalSmallModel.StrictLocalMateProjectionFormulas, use its explicit theorem
name. StrictLocalSmallModel.StrictLocalLocalizedHomGerm now directly publicly imports
StrictLocalSmallModel.CohomologyGerms, which supplies the small-model source legs
occurring in its statement. Removing the old indirect import exposed its missing
direct dependency (unknown smallModel_strictLocalCohomologySourceLegs and its app
lemma at lines 146, 155 and 186). All six adapted modules are unclaimed.
Their public declaration signatures
and mathematical definitions stay identical. Reattach the existing item node to
the retained theorem and update its proof route and the two caller proof plans that name it.
No source-library module or target declaration is changed.

The disposable Lean validation probe checks all five old construction bodies
against the adopted constructions by rfl, and applies the new theorem to the full
original theorem type. The proof handles arbitrary integer degrees, zero complexes,
and empty schemes just as before, and makes no etaleness or acyclicity assumption
on the small-model cone legs or limit pullback. No unit statement or route changes.

Change record: coord/changes/E2-retire-etale-injective-sections-comparison.md,
including all 24 live downstream users, exact old/new modules and model distinctions.

## Proved and sorry left

Holes closed: none (the assigned retirement item started with zero).
Holes added: none. Holes left in delivered modules: none.
The retained smallModel_injectiveSections_strictLocal_comparison is fully proved;
it is the existing obligation at
lem-weil-pbc-injective-sections-pullback-comparison, not a split-off theorem.
The original five constructions remain the adopted source's actual constructions.

The construction/signature validation probe compiled without warnings.
`#print axioms` for the retained theorem lists exactly propext, Classical.choice
and Quot.sound. The full rebuilt set passed without warnings: 26/26 modules,
comprising the retained theorem, the disposable validation probe, and all 24
live downstream consumers. Maximum compile time was 57.2 seconds, within the
60-second per-file limit. The probe is excluded from the delivery. Byte-identical consumer sources remain
in the compile set because the published artifacts predate some of their current
small-model names; they are excluded from the commit. A delivery compile with only
the seven changed files exposed this stale-dependency mismatch, so the delivery
also rebuilds the same unchanged consumers already validated above. An additional full-source rebuild checked the retained comparison, the derived
mate factorization, the derived restriction theorem and the final projection
assembly theorem explicitly: all four use exactly the three permitted axioms.
The isolated factorization axiom probe subsequently passed as well.
The six adapted consumers retain every original
declaration signature (also checked by the project declaration parser).

## No longer needed

Withdraw lean/Sheaf/AlgebraicGeometry/EtaleInjectiveSectionsComparison.lean and
replace both live direct imports. The five duplicate construction declarations
and the duplicate private isIso_representativeSectionsComparison_of_etale proof
are unnecessary; the adopted source owns those constructions and its complete
etale stage comparison is reused. The old small-model theorem remains, renamed
and reattached, so its DAG node and all its parent dependencies remain needed.
There is no claim that the canonical-model source theorem equals the small-model
cone-leg assertion.

The new focused theorem module does not need the old public import
Sheaf.AlgebraicGeometry.StrictLocalSmallModel.CohomologyGerms: its statement uses
only neighbourhood geometry and the adopted sections constructions.
StrictLocalLocalizedHomGerm now imports CohomologyGerms directly where its public
source-leg formula actually uses it; that module remains needed. The former
private TorsionAcyclic import is no longer direct: the adopted comparison theorem
already supplies its fully proved etale-injectivity argument, and still imports
TorsionAcyclic itself. These source dependencies are not pruned from the library.
The geometry transport and arbitrary triangle naturality remain required. There
are no other nodes or modules made unnecessary by this packet.

## Where the brief, the DAG or earlier work was wrong

The current source is already proved; this is the zero-hole retirement repair
identified by the queue, covered by the brief's repair exception. The old twin
census cannot be read as permission to replace the entire statement: its common
constructions are exact duplicates, while the last conjunct
of its theorem is not an exact duplicate: the adopted theorem uses
strictLocalizationToBase and Q.legs, and the existing consumers need
strictHenselizationStructuralMap and Q.smallModelLegs. Substitution of the source
cone-leg assertion would change the statement; this packet retains the complete
small-model assertion and proves it using the shared triangle theorem.

Searches actually run through msearch.py: LeanFinder for the termwise/derived
sections comparison (8 general injective-resolution hits), Loogle for
CategoryTheory.NatTrans.naturality (9 hits), and grep for
rightDerivedFunctorUnit|isKInjective_of_injective (9 hits). Local searches found
the adopted comparison and triangle theorem, read in full. No new nodes are needed.
Historical quarantine snapshots of already-retired source-section twins are not
current rework entries; this repair neither deletes nor modifies those archives.

## Second reading by E2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
