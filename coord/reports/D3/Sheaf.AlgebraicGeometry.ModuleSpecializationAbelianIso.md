## What changed

Restored Sheaf.AlgebraicGeometry.ModuleSpecializationAbelianIso from the archive
named in coord/rework.tsv, preserving all declaration signatures and docstrings.
Its private strictLocal_germ proof now uses the existing generic section-cone
restriction specialized by strictLocalSectionCone and strictLocalNeighbourhoodSection.
The main proof uses the actual small-model structural-map equation from
exists_strictHenselizationStructuralMap, rather than the old short equation name.
The retired derived coefficient comparison import is replaced by the canonical
WeilConjectures.AlgebraicGeometry.ModuleAbelianCoefficientComparison.

The complete proof compares the module and abelian maps on each pointed affine
germ, using the coefficient/stalk comparison and naturality in the sheaf isomorphism.
Colimit extensionality identifies the maps, and reflection of isomorphisms through
the coefficient functor gives bijectivity. No hypotheses or definitions change.

The current DAG already records this exact generic-cone route and the canonical
coefficient functor. Its statement, attachment, proof dependencies and unit route
are preserved. No new node is needed. The change record is
coord/changes/D3-restore-module-specialization-abelian-iso.md.

Searches used msearch leanfinder, loogle and grep, and rg in both library roots
and Mathlib. Lean Finder returned structure-sheaf specialization and tilde-germ
lemmas, not this etale module comparison. Loogle did not resolve the unqualified
sheafFiberCompIso name; direct Mathlib inspection found the existing filtered
colimit comparison and germ equation used by the archived proof. The preserved
proof is already an argument from those general comparison lemmas.

## Proved and sorry left

This is a zero-hole restoration and API repair. The archived item contains zero
sorrys and the restored item contains zero. Holes closed: 0. Holes added: 0.
Split off: 0. No remaining sorry declaration exists in this delivery.

The complete public theorem is
AlgebraicGeometry.Etale.bijective_moduleSpecialization_of_abelianIso
(node lem-weil-pbc-module-specialization-abelian-iso). The private helpers
pullback_germ and strictLocal_germ are also completely proved. The item compiled
with lcompile.py within the single-file limit (8.3 seconds in the final check).
A temporary consumer probe also compiled (4.6 seconds), applying the theorem with
its unchanged signature and checking by rfl that strictLocalSpecialization equals
etaleStalkSpecialization. The probe's #print axioms reports exactly propext,
Classical.choice and Quot.sound. The probe was removed before delivery.

## No longer needed

The archived public import
Sheaf.AlgebraicGeometry.ModuleAbelianDerivedDirectImageComparison is replaced
by WeilConjectures.AlgebraicGeometry.ModuleAbelianCoefficientComparison: only
the coefficientwise forgetful sheaf functor is required, not derived direct images.
The retired specialized restriction names are replaced by the already stated
PointedEtaleSectionCone and StrictLocalSectionCone APIs. Those nodes are already
the current proof dependencies, so no DAG pruning or new split is claimed.

All other item imports are used. SmoothProperPrimeSpecialization supplies the
strictLocalSpecialization definition in the statement; its smooth-proper theorem
is not used in this comparison. No Lean module is withdrawn, and no source-library
declaration, parent dependency or blueprint unit step is removed.

## Where the brief, the DAG or earlier work was wrong

The source is absent because of quarantine, not withdrawal. This assignment has
zero holes and requires restoring a compiling implementation, not closing a new
sorry or reassigning the obligation. The archived proof uses retired interfaces;
the live dependencies already contain the A3 generic restriction repair. The
current DAG is consistent with the repaired proof and needs no change.

The direct quarantined parent ProperSmoothCurvesPrimeCoefficients still uses the
item in prime_invertible_constructible, and its DAG dependency remains. Its call
was checked against the unchanged signature. No live consumer exists and no
consumer adaptation is needed. The archived module and its DAG attachment remain
preserved; no deleted.txt is created.

## Second reading by D3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
