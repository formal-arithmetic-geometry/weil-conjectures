## What changed

Restored Sheaf.AlgebraicGeometry.ModuleSpecializationAbelianIso from the quarantine
path recorded in coord/rework.tsv. Preserved its theorem signature, declarations,
docstrings and germ/colimit proof. The archived proof now uses the current generic
PointedEtaleSectionCone restriction, specialized by strictLocalSectionCone, and the
small-model structural-map leg equation from exists_strictHenselizationStructuralMap.
The retired coefficient-comparison import is replaced by the canonical upstream
ModuleAbelianCoefficientComparison, which defines the identical moduleAbelianForget.

Repaired two unclaimed dependencies: SmoothProperPrimeSpecialization now constructs
strictLocalSpecialization using the unique generic-cone restriction for the same small
strict-local model; SpecializationCospecializationArrows uses that API in its existing
etaleStalkSpecialization_naturality proof. All signatures are unchanged. Added the
explicit public UpperLowerStarCoherence import needed by existing public statements
in SmoothProperPrimeSpecialization and ProperLocallyAcyclicSpecialization.

The item node retains its attachment and statement. Its proof dependencies now name
the general section-cone API and its small-model realization instead of the retired
specialized restriction interface; the original unit route remains intact.

Change record: coord/changes/A3-module-specialization-generic-restriction.md.

Validation: the item, all three adapted dependencies and the unchanged direct consumers
StrictBaseFibreMapFactorization and SpecializationCospecializationCompatibility compiled
with lcompile.py, each within the single-file limit. A temporary Lean probe checks by
rfl that repaired strictLocalSpecialization equals etaleStalkSpecialization, and prints
the axioms of the specialization definition, specialization naturality and the restored
comparison theorem: each uses only propext, Classical.choice and Quot.sound.
The probe is excluded from the delivery.

The search for a shorter route used msearch leanfinder, loogle and grep, plus rg in
both library roots. Lean Finder returned topological/structure-sheaf specialization
facts, not the etale module comparison. Loogle found the Mathlib sheafFiberCompIso
and its germ compatibility lemmas already used by this proof. The preserved colimit
argument supplies the required comparison of the specific specialization maps.

## Proved and sorry left

This is a zero-hole restoration/API repair, not a new hole closure or a decomposition.
The quarantined item already had zero textual sorrys; the repaired item has zero.
Holes closed: 0. Holes added: 0. Split off: 0.

The restored complete theorem is
AlgebraicGeometry.Etale.bijective_moduleSpecialization_of_abelianIso
(node lem-weil-pbc-module-specialization-abelian-iso). Its two private germ helpers
remain fully proved. The repaired naturality theorem is
AlgebraicGeometry.Etale.etaleStalkSpecialization_naturality. No sorry remains in any
of the four delivered Lean modules, and no new theorem or definition is introduced.

## No longer needed

The archived item's import
Sheaf.AlgebraicGeometry.ModuleAbelianDerivedDirectImageComparison is unnecessary:
only the coefficientwise forgetful sheaf functor is used, supplied by upstream
WeilConjectures.AlgebraicGeometry.ModuleAbelianCoefficientComparison. No derived
direct-image comparison is used in this germ argument.

SmoothProperPrimeSpecialization no longer imports the withdrawn
Sheaf.AlgebraicGeometry.StrictHenselizationRestriction. It imports
Sheaf.AlgebraicGeometry.StrictLocalSectionCone instead. The item's proof no longer
uses the official-model node def-weil-pbc-strict-henselization-restriction; its correct
small-model dependencies are def-weil-pbc-pointed-etale-section-cone and
def-weil-pbc-small-strict-local-section-cone. The smooth-proper specialization node
remains needed for its specialization definition. No module or DAG node is withdrawn,
and no pruning of the blueprint unit's statement or steps is claimed.

## Where the brief, the DAG or earlier work was wrong

The item is absent from lean/ because it is quarantined, not because it was withdrawn.
The archived item contains a complete proof and zero holes; its assigned repair is
to restore a compiling implementation against current interfaces.

Earlier retirement work left small-model specialization consumers using the removed
specialized restriction names. The upstream restriction API now uses strictLocalization,
which is not definitionally the small strictHenselizationScheme in these statements.
The repair uses the reviewed generic section-cone construction, preserving the actual
small scheme, limit legs and unique germ equations. In addition, the old short name
strictHenselizationStructuralMap_eq now refers to the official-model equation;
the restored proof instead uses the correct small-model choose_spec equation.

The initial compile failed in SpecializationCospecializationArrows on the unknown
existsUnique_strictHenselizationStalkRestriction. Its current proof needed the same
API migration as the item. A later consumer compile found rightDerivedLowerStarPlus
private in the public statement of ProperLocallyAcyclicSpecialization (line 300);
the defining coherence module is now imported publicly. None of these defects is a
false mathematical statement or a reason to change a target.

## Second reading by A3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
