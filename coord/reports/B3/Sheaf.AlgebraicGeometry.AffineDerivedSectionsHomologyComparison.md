## What changed

Proved AlgebraicGeometry.affineDerivedSections_homology_comparison with its signature
unchanged. Its proof composes the canonical lower-truncation projection, the comparison
for the truncated object, and the supplied hG isomorphism.

Added two proved helper modules: AffineDerivedSectionsTruncationIso applies the existing
unbounded bound with N = 1 to the negative tail, using affine-open module cohomology
vanishing. Exact postcomposition with forgetting modules compares derived functors;
conservativity detects the cohomology isomorphism. AffineDerivedSectionsTruncatedBottom
lifts truncGE to D+, applies the existing truncLE comparison, identifies the double
truncation with a single complex, then composes shifts and rightDerivedZeroIsoSelf.
This helper holds on the entire derived category, without quasi-coherence.

The proofs follow the successive equalities at https://stacks.math.columbia.edu/tag/06Z0
and the bounded below calculation at https://stacks.math.columbia.edu/tag/05TC.
The source files are absent from this clone, so the primary-source pages were read directly.
Single-file compiles and import-direction checks passed. The final dry run recompiles the set.

## Proved and sorry left

Closed the one original hole: AlgebraicGeometry.affineDerivedSections_homology_comparison
(lem-pc-affine-derived-sections-homology-comparison).
Also proved AlgebraicGeometry.affineDerivedSections_truncGE_isIso
(new-affine-derived-sections-truncation-iso) and
AlgebraicGeometry.affineDerivedSections_truncated_bottom
(new-affine-derived-sections-truncated-bottom).
No sorry remains in any delivered module; zero new or split-off holes.
The proofs use existing library statements, including
CategoryTheory.Functor.isIso_homologyFunctor_rightDerivedFunctorPlus_truncLEι,
which is still sorry in its existing module. This does not claim a sorry-free transitive closure.

## No longer needed

Removed the item's direct proof imports
WeilConjectures.AlgebraicGeometry.Cohomology.Affine.Cech and
Sheaf.AlgebraicGeometry.UnboundedDerivedFunctorCohomologicalBound, replacing them with
the two actual comparison steps. Their original dependencies remain needed below the
truncation helper; no entire original dependency branch is pruned. In particular,
lem-pc-affine-vanishing, lem-pc-unbounded-derived-functor-cohomological-bound and
lem-weil-pbc-affine-tilde-gamma-adjunction remain reached as tools or statement dependencies.
No globally pruned module is claimed. No unit statement or step is bypassed.

Removed the exploratory Mathlib.CategoryTheory.Preadditive.LeftExact import from the new
bottom module because its API comes through RightDerivedFunctorTruncationIso.
No abandoned scratch module is included.

## Where the brief, the DAG or earlier work was wrong

The plan was usable. Its affine vanishing declaration computes abelian-sheaf cohomology,
whereas the cohomological bound uses derived sections on module sheaves. The proof uses
existing affine-open module-cohomology vanishing and its comparison to bridge those carriers.
The lowest-degree bounded below calculation needs only left exactness, not quasi-coherence.
The direct degree-n argument avoids shifting the unbounded tail.
Edge cases include the zero ring, zero object, every integer cutoff and unbounded K.
LeanSearch returned Internal Server Error; LeanFinder, Loogle and source grep were available.

## New nodes

new-affine-derived-sections-truncation-iso: the actual canonical projection is invertible
on derived sections in degree n; proved in
lean/Sheaf/AlgebraicGeometry/AffineDerivedSectionsTruncationIso.lean.

new-affine-derived-sections-truncated-bottom: the natural lowest-degree comparison after
lower truncation on the whole derived category; proved in
lean/Sheaf/AlgebraicGeometry/AffineDerivedSectionsTruncatedBottom.lean.
Both retain the item's chapter, unit and blueprint ancestry. No change record is needed:
no existing public statement or definition changed.

## Second reading by B3

1. Compared the delivered target module with the repository version. The theorem signature is byte-for-byte unchanged; only proof imports and proof terms changed. Verdict: pass.

2. Compiled all three delivered modules with `lcompile.py --all`; they compile cleanly. There are no `sorry`s in the delivered files, and no forbidden `axiom`, `unsafe`, `opaque`, `implemented_by`, or `extern` declarations. Verdict: pass.

3. Checked both split-off statements against their Lean declarations and DAG nodes. Each is a true strict intermediate comparison needed by the target, with complete natural-language proof descriptions and no weakened target statement. Verdict: pass.

4. Reviewed the proof route and imports. The target composes the canonical truncation comparison with the bounded-below comparison and the supplied `hG`; the removed direct Cech and unbounded-bound imports are replaced by the actual helper imports. Verdict: pass.

5. Checked node metadata and the unit route. The target and both new nodes retain chapter and unit ancestry, and their proof/proof_deps records match the Lean proofs. Verdict: pass.

Changed only the three delivered modules, their two new DAG nodes, and this report; no public statement or definition was changed.
