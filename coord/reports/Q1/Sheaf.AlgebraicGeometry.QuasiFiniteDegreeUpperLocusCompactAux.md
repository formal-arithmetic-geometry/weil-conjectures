## What changed

The unchanged target `AlgebraicGeometry.Scheme.Hom.exists_compact_open_successor_degree_locus_inter_affine` now constructs the supremum of finitely many basic opens, proves its compactness with `IsAffineOpen.isCompact` and `Set.Finite.isCompact_biUnion`, and proves the required carrier equality pointwise. Its sole added import is the proof-only `Sheaf.AlgebraicGeometry.QuasiFiniteDegreeSublevelFiniteEquations`. Both original public imports remain unchanged.

The finite-equations descent step is isolated in that new module. The parent node now records the reduction actually written in Lean. No existing signature, definition, visibility, or target statement changes; no change record or forced adaptation is needed.

## Proved and sorry left

Hole closed: `AlgebraicGeometry.Scheme.Hom.exists_compact_open_successor_degree_locus_inter_affine` (node `lem-weil-pbc-qf-degree-successor-affine-compact-aux`). No sorry remains in the item module.

Hole added: `AlgebraicGeometry.Scheme.Hom.exists_finite_equations_degree_sublevel_inter_affine` (node `lem-weil-pbc-qf-degree-sublevel-finite-equations`), whose whole proof is `by sorry`. No other hole is added. This is a decomposition: one upper hole closed and one lower hole added, net zero holes. The target still depends on `sorryAx` through that intermediate theorem and is not fully proved without sorry.

## No longer needed

No repository import was removed and no module is claimed pruned. The worker's redundant added `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact` import was removed by the second reader; compilation confirms that the original public imports already expose the required compactness facts.

The parent node no longer directly uses `lem-weil-pbc-descend-finite-locally-free` or `lem-weil-pbc-spec-colimit-limit`; both remain needed through the finite-equations node. The old dependency `lem-weil-pbc-spec-basic-opens-unit-ideal-quasi-compact` remains represented by the affine basic-open compactness argument. The new finite-equations node does not need that compactness dependency, since its conclusion stops at the pointwise finite-equations criterion.

## Where the brief, the DAG or earlier work was wrong

The original DAG compressed descent and the compact-open construction into one step. The delivered proof formalizes the latter and leaves the former open. The first worker did not update the parent's proof record, and incorrectly reported removal of helper imports that were absent from the repository version. Its new node cited compactness unnecessarily and recorded searches not matching its search log. The second reader repaired these records and repeated the searches.

The local literature checkout lacks `literature/stacks-project/more-morphisms.tex`; the second reader read the cited source at https://stacks.math.columbia.edu/tag/07RZ. Its second proof paragraph explicitly gives the finite-equations descent followed by the finite union of standard opens. No unit route is replaced.

## New nodes

`lem-weil-pbc-qf-degree-sublevel-finite-equations`, in `dag/nodes/sec-proper-base-change/`, states the finite-equations step of Tag 07RZ. Its self-contained statement and Lean record agree. Its docstring explains the closed ideal, filtered quotient system, descent of finite local freeness with degree, equality of vanishing loci, and choice of finite generators. Its proof dependencies are `lem-weil-pbc-descend-finite-locally-free` and the Mathlib leaf `lem-weil-pbc-spec-colimit-limit`. This still-open step requires substantial scheme and quotient-diagram construction; it cannot be closed by a short application of the already-proved general descent theorem.

## Second reading by Q1

1. PASS: compared the item against the repository with `diff`; its existing declaration signature and docstring are byte-for-byte unchanged. Changes are a proof and a proof-only import. There are no data definitions or other existing declarations in the delivery.
2. PASS with one reported open dependency: both modules compile locally with no errors or warnings. The only textual sorry is the whole proof of the named finite-equations theorem. Explicit `#print axioms` checks show only the permitted standard axioms and `sorryAx`; the delivery tool also probes all declarations. No forbidden declarations or hollow definitions occur.
3. PASS: the finite-equations theorem is the descent part of the cited source, strictly preceding the compactness argument. The item contains a real compact-open construction and equality proof, rather than an application of a renamed copy of its conclusion. Empty W is vacuous and permits an empty finite set; a sublevel locus equal to W permits the zero ideal and empty generating set; an empty sublevel locus permits the unit ideal and generator 1. The arithmetic complement equivalence also holds at r=0. Repeated LeanFinder, Loogle, and grep searches (LeanSearch returned Internal Server Error and is recorded as unavailable), and direct searches of both Lean roots, found generic affine compactness facts but no existing finite-equations theorem with these hypotheses. General descent is available, but applying it requires construction of the filtered quotient diagram and its limit.
4. PASS: the shortest elementary construction uses affine-basic-open compactness already available from the original imports. Removed the redundant added QuasiCompact import. The revised No longer needed section exhausts the old proof dependencies and distinguishes direct dependencies from those retained in the split node. Read `dag/units/sk-thm-p1.json`, including `realized`: none of its statement or step realizers is bypassed or changed; the Tag 07RZ descent route stays intact.
5. PASS after repair: updated the parent node's proof, proof_deps, and proof_origin to match the actual reduction. Made the new node statement self-contained, removed its unused compactness proof dependency, and replaced search records with queries actually run and logged. Its Lean declaration record matches the source signature. New-node provenance, source, chapter, unit, blueprint link, and creation fields are present.

Changes by the second reader: removed one redundant proof import; repaired parent proof metadata, split-node statement/dependencies/search evidence, and the progress/pruning report. The Lean proof itself required no repair.
