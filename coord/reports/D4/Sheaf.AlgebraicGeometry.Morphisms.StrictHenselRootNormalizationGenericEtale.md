## What changed

Simplified the proof in
Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRootNormalizationGenericEtale.
The private small_strictHenselization_structural_flat now applies the existing
strictHenselization_indEtale_of_affine_chart to the identity chart of Spec R.
The given equality hb supplies its structure-map compatibility; the spectrum
isomorphism is the identity. Forget its filtered etale algebra presentation to
modules and apply ModuleCat.flat_of_colimitPresentation, since etale algebras
are flat. This replaces the repeated construction of the neighbourhood ring
cocone and its compatibility equations with an application of the library API.
The helper keeps exactly the same signature.

Replaced the private proof import
WeilConjectures.RingTheory.ProEtale.FaithfullyFlat with
Sheaf.AlgebraicGeometry.StrictHenselizationAffineChartIndEtale, which publicly
exports the required flat-colimit theorem. Updated the item's existing DAG node
proof, proof_deps and proof_origin to record this argument.

The public theorem signature and public imports were compared verbatim with the
current source and are identical. No definition, statement, public declaration,
source-library module or consumer was changed. No change record is required for
these proof-only changes. The canonical small coordinate-ring construction and
the generic-etaleness and finite-morphism shrinking arguments are preserved.

## Proved and sorry left

The current item already had 0 local holes when this worker started. F3's
restoration had landed on 2026-10-20. This delivery simplifies that complete
proof; it does not claim a further hole closure or a new restoration.

0 of 0 local holes closed; 0 added, 0 split off, 0 remain.
AlgebraicGeometry.Scheme.GaloisCover.strict_hensel_root_normalization_generic_etale
(node lem-sbc-strict-hensel-root-normalization-generic-etale) and the private
small_strictHenselization_structural_flat are fully proved. The remaining private
helper etale_shrink_of_fibre_source_opens is unchanged and fully proved.

The module compiles through lcompile.py in 2.3 seconds, with no warnings.
Explicit #print axioms checks for the public theorem and the rewritten private
helper report exactly propext, Classical.choice and Quot.sound, so neither has a
transitive sorry dependency. The diagnostic print commands were then removed.
The import-direction check accepts the affine-chart theorem import. All lines
are at most 100 characters. The chapter and unit route are unchanged.

## No longer needed

The explicit proof import
WeilConjectures.RingTheory.ProEtale.FaithfullyFlat is removed; it remains available
through the affine-chart theorem's public imports and is still needed for the
flat-colimit result. No claim of pruning that module from the target closure is
made.

This item's direct proof edge to lem-weil-pbc-flat-ring-map-iff-ind-flat is no
longer needed: the new helper uses the existing algebra presentation directly,
then lem-weil-pbc-flat-colimit-presentation-same-universe. Added the direct proof
edge to lem-weil-pbc-strict-henselization-affine-chart-ind-etale. The former
private neighbourhood-cocone construction and its equations are removed. All
other stated dependencies remain used. No library modules are withdrawn or
newly pruned, and no incoming DAG dependency is removed.

## Where the brief, the DAG or earlier work was wrong

The rework row still records the old quarantined failure involving
strictHenselization_structural_ringHom_flat, but the current source and node
already contain F3's complete restoration. The archived failure is not a current
compiler error. The starting module compiled cleanly in 4.7 seconds and had no
local holes. The assigned deep chain also has no transitive sorry dependency in
the resulting theorem, as checked above. The work here is a shorter proof using
an existing declaration, not another split or an unfinished repair.

The affine-chart theorem is a tool applied to the identity chart; it does not
change the root-extension or generic-etaleness route. Its hypotheses hold for
any geometric point of Spec R, with no nonemptiness assumption added: the point
itself supplies the witness for membership in the identity map's range. The
compatibility equation simplifies exactly to hb. No new statement or arbitrary
construction from an unproved existence theorem is introduced.

Searches were run with msearch.py: LeanFinder for etaleness near a finite fibre,
Loogle for AlgebraicGeometry.Etale and AlgebraicGeometry.IsFinite, and grep for
flatness of colimits. Those searches returned general etale-locus or unrelated
results. Direct library searches found the existing small-ring affine-chart
ind-etaleness theorem and the proved flat-colimit presentation API. Their actual
signatures, the item's declared dependencies and the unit record were read.

## Second reading by D4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
