## What changed

Replaced the sorry in
`AlgebraicGeometry.Scheme.Modules.coherent_kernel_ideal_intersection_bound`
with a compiling finite-affine-cover argument. The signature and all existing public
imports are unchanged. New proof imports are AffineIdealIntersectionInclusion,
CoherentFiniteTypeLocallyNoetherian, CoherentAffineSectionsFinite,
Mathlib.RingTheory.Filtration, and WeilConjectures.AlgebraicGeometry.Modules.FreeGenerator.
Repair of the duplicate-theorem return: removed both private helpers app_injective and
range_of_locally_range. The proof now directly applies Mathlib's
ModuleCat.mono_iff_injective, TopCat.Sheaf.existsUnique_gluing', and
TopCat.Sheaf.eq_of_locally_eq' to the local lifts for the particular kernel product
inclusion. It declares no replacement helper theorem.
Updated the assigned node's proof route to match the Lean.

The argument proves finite affine generation, applies Mathlib module Artin-Rees, takes
the maximum over a finite affine subcover, proves the ideal-power inclusion for m=c+n,
and glues local preimages. The affine comparison at fixed exponents is split off into
one new module. There are no definition, interface or target changes and no adaptations.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.Scheme.Modules.coherent_kernel_ideal_intersection_bound`
(node lem-pc-coherent-kernel-ideal-intersection-bound). No sorry remains in the assigned module.

Added one hole:
`AlgebraicGeometry.Scheme.Modules.affine_ideal_intersection_inclusion`
(node lem-pc-affine-ideal-intersection-inclusion), in
Sheaf.AlgebraicGeometry.AffineIdealIntersectionInclusion.
This is a decomposition, with one upper hole closed and one strictly geometric hole added,
not a completed proof without sorry dependencies. The lower statement assumes an algebraic
inclusion on one affine open at two fixed exponents; it has no Noetherian or coherence
hypotheses and proves no existence or uniformity of a bound. All compactness, Artin-Rees,
exponent arithmetic and global gluing are proved in the assigned module.

Both delivered modules compiled with lcompile.py --all, without warnings. The empty cover
uses Finset.sup=0; descent also covers empty W. The new statement allows zero exponents,
zero modules, and zero or unit ideals: affine exactness and tensor comparison include
these cases, and the recursive zeroth power is the unit. Neither H nor its coherence
is used by the reduction. No arbitrary mathematical object is chosen from an unproved
existence theorem: the proof chooses only proved module bounds and local preimages.

## No longer needed

Removed the two duplicate helper declarations app_injective and range_of_locally_range;
no replacement declarations are added. No original import was removed: each is part of
the existing public statement context.
The attempted proof-only import of Sheaf.AlgebraicGeometry.CoherentArtinRees was removed.
This item's route no longer uses lem-weil-pbc-coherent-artin-rees
(Sheaf.AlgebraicGeometry.CoherentArtinRees), nor its equality-comparison step
lem-weil-pbc-artin-rees-affine-comparison
(Sheaf.AlgebraicGeometry.ArtinReesAffineComparison), nor its ideal-power-factor step
lem-weil-pbc-formal-module-ideal-power-factor
(Sheaf.AlgebraicGeometry.CoherentFormalModule).
Only the inclusion comparison is needed, not the Artin-Rees subsheaf equality or the
formal quotient factorization. These may remain needed by other targets or items.
The lower geometric comparison still needs the ideal-product, quasi-coherent kernel
and image theories; these are not claimed to be pruned.

## Where the brief, the DAG or earlier work was wrong

The returned delivery duplicated two private theorems in CoherentArtinRees.
Those declarations are genuinely the same statements, not a binder ambiguity.
They cannot be reused through an import: they are private and the import is cyclic.
The repaired proof instead uses the existing public Mathlib evaluation, injectivity
and gluing theorems directly for its constructed lifts, with no duplicate declarations.
The previous second reading concerned the returned version and has been removed;
the independent reader must review this repair.

The DAG's two-line plan using coherent_artin_rees is mathematically correct but cannot
be imported here: import_direction.py reports a source import cycle. The shortest path is
CoherentArtinRees -> ArtinReesAffineComparison ->
Modules.IdealTimesQuasiCoherentAffineSections ->
WeilConjectures.AlgebraicGeometry.Modules.ClosedImmersion ->
WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage ->
WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.FiniteFreeComplex ->
IntegralIdealProperCohomology -> IntegralIdealComparisonFiltrations ->
IntegralIdealCommonSubmodule -> RankOneGenericIdealInclusion ->
GenericIdealStalkEmbeddingExtension -> LocalClosedIdealMapExtension ->
ClosedStructureAmbientIdealExtension -> IdealPowerTensorImageLift -> the assigned module.
No unrelated modules were edited to break it. The new comparison has only acyclic
statement imports, and the actual proof uses acyclic existing finite-generation modules.

The unit sk-thm-picard-coherence has no realized binding for this auxiliary node;
its proper-cohomology route is preserved. The replacement is below the unit level.
Read Stacks Tags 01YA, 01I8 and 01IC online because this clone lacks the Stacks source
files. The docstrings and node give the source and full geometric proof for the remaining
step. LeanFinder and grep found no exact comparison; LeanSearch was unavailable.

## New nodes

lem-pc-affine-ideal-intersection-inclusion: the geometric fixed-exponent affine comparison,
with one named sorry in its own new module. It is strictly a part of the original argument,
not a restatement of the kernel-bound theorem. Its source is the affine reduction in
Stacks Tag 01YA and the tensor/exactness results 01I8 and 01IC. Its node records semantic
search, unavailable LeanSearch, and local/blueprint grep. There are no change records.

## Second reading by Q2

1. I compared the delivered item module with the repository version. The theorem signature and all existing declarations are unchanged; only the proof and proof-only imports differ. Verdict: pass.

2. I compiled both delivered modules with `lcompile.py --all`; compilation succeeds. The item theorem has no `sorry`; the intentionally split affine comparison has exactly its named `sorry`, with no forbidden axiom or hollow definition. Verdict: pass.

3. The split statement `affine_ideal_intersection_inclusion` is a true fixed-exponent affine comparison, strictly weaker and simpler than the uniform kernel bound. It allows zero exponents and degenerate modules and has the required source, proof docstring, and DAG node. Searches found no existing declaration with this statement. Verdict: pass.

4. The proof uses Mathlib Artin--Rees, finite affine sections, and direct sheaf gluing. It removes the cyclic `CoherentArtinRees` route and duplicate private helpers while preserving the unit route; no old proof dependency is used without being reported. Verdict: pass.

5. The item node proof, dependencies, and origin match the Lean proof, and the new node records its declaration and searches. Verdict: pass.

Changed during second reading: restored the required proof-only `FreeGenerator` import (which supplies `Hom.app_presheaf_map`) after a minimal-import experiment showed the proof depended on it. No theorem statement or definition changed.
