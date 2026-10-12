## What changed

Replaced the sorry in `AlgebraicGeometry.Scheme.Modules.invertS_cohomology` with the
09MR induction argument: choose the nonvanishing open, prove the comparison for every
affine open, apply the existing Mayer--Vietoris gluing implication, and apply the
existing quasi-compact-open induction theorem at the compact top open. The final
transport along `⊤ ⊓ S = S` preserves the displayed canonical numerator formula.
The original theorem signature and visibility are unchanged.

Added `Sheaf.AlgebraicGeometry.AffineOpenCohomologyLocalization`, whose theorem
`AlgebraicGeometry.Scheme.Modules.affineOpen_cohomology_localization` is proved from
its degree-zero case and affine vanishing. For positive degrees, the numerator groups,
the direct sum and its quotient, the target, and the twisted target groups are all
subsingletons. The equivalence is explicitly constructed from zero maps; no data is
chosen from an unproved existence statement.

Added `Sheaf.AlgebraicGeometry.AffineOpenCohomologyLocalizationZero` for the remaining
degree-zero restriction/presentation bridge to `affine_section_localization`. Its
statement requires only an affine open of X, not an affine ambient scheme or compactness
of X. Its docstring gives the full restriction, derived-degree-zero, quotient and
canonical-formula argument. The main module adds proof imports of the ambient affine
lemma and `Sheaf.Paper.NonvanishingSectionTrivializes`; all pre-existing public imports
are unchanged. Updated the main node's proof and dependencies to match this route.

Validation: all three sandbox modules compile together with lcompile.py without errors
or warnings. Checked empty U, zero s and p = 0 in the mathematical argument. Consulted
Stacks Tags [09MR](https://stacks.math.columbia.edu/tag/09MR),
[01PW](https://stacks.math.columbia.edu/tag/01PW) and
[01E1](https://stacks.math.columbia.edu/tag/01E1) online because the literature source
files are absent from this clone. LeanSearch returned HTTP 500; recorded unavailable,
not a negative result. LeanFinder, Loogle and source grep were also run.

## Proved and sorry left

Closed the item's one original hole:
`AlgebraicGeometry.Scheme.Modules.invertS_cohomology`
(node `lem-sc-invert-s-cohomology`). No sorry remains in the item's module.

Also proved the new intermediate theorem
`AlgebraicGeometry.Scheme.Modules.affineOpen_cohomology_localization`
(node `lem-sc-invert-s-cohomology-affine-open`), including its positive-degree argument.

Added one hole, the entire proof of the public theorem
`AlgebraicGeometry.Scheme.Modules.affineOpen_cohomology_localization_zero`
(node `lem-sc-invert-s-cohomology-affine-open-zero`). This is strictly the degree-zero
affine-open base case, without either the positive-degree argument or the global
Mayer--Vietoris/induction argument. Thus this delivery is a decomposition of the global
hole, not a claim that the full localization theorem is axiom-free. Holes closed: 1;
holes added: 1; net: 0. Existing imported holes are unchanged.

## No longer needed

Removed the direct proof import `Sheaf.AlgebraicGeometry.AffineCohomologyLocalization`.
The main node no longer uses `lem-sc-invert-s-cohomology-affine-case`; the ambient affine
argument uses its narrower degree-zero section input and proves positive degrees.
The integer-power theorem `lem-sc-invertible-tensor-qcoherent` and its planned
quasi-coherent tensor-product dependencies are not needed: every numerator degree is
nonnegative, and the already proved `isQuasicoherent_tensorObj` handles those twists.

The following project modules disappear from this item's import closure (computed
from repository imports with the delivered sources overlaid):

- `Sheaf.AlgebraicGeometry.AffineCohomologyLocalization`
- `Sheaf.AlgebraicGeometry.InvertibleTensorQcoherent`
- `Sheaf.AlgebraicGeometry.QuasiCoherentTensorProductAffineSections`
- `Sheaf.AlgebraicGeometry.Modules.AffineTildeTensor`
- `Sheaf.AlgebraicGeometry.Modules.AffineTildeTensorStalk`
- `Sheaf.AlgebraicGeometry.Modules.RestrictionTensorComparison`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.StalkTensor`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct`
- `Sheaf.Algebra.Homology.ModuleStalkFunctor`
- `Sheaf.LinearAlgebra.TensorProduct.ColimitVaryingRings`
- `Sheaf.Topology.PresheafModuleStalkFunctor`

This is pruning from this item's route; these modules may still be needed by other
branches of the targets. No unit statement or realized unit step is bypassed. The
09MR affine / Mayer--Vietoris / induction route is retained.

## Where the brief, the DAG or earlier work was wrong

The existing affine-case declaration is stated on an affine scheme at its top open,
whereas the induction hypothesis must be stated on arbitrary affine opens of the
ambient X, with the ambient openModuleCohomology and its restriction maps. It cannot
be applied directly to the induction predicate. Existing OpenModuleCohomologyComparison
gives Nonempty additive equivalences with abelian-sheaf cohomology but does not provide
the naturality and fraction-generator formulas needed to transport this statement.
The new degree-zero node isolates this exact gap. No existing statement was changed
or marked disputed. The quasi-compact-open induction node is already proved in the
current repository and was reused, not re-proved.

## New nodes

`lem-sc-invert-s-cohomology-affine-open`:
`lean/Sheaf/AlgebraicGeometry/AffineOpenCohomologyLocalization.lean`, proved. This is the
affine-open base case in the ambient cohomology convention. Its proof uses the new
zero case, existing affine-open vanishing and affineness of the nonvanishing intersection.

`lem-sc-invert-s-cohomology-affine-open-zero`:
`lean/Sheaf/AlgebraicGeometry/AffineOpenCohomologyLocalizationZero.lean`, sorry. This is
only the p = 0 affine-open comparison, with its fraction formula. The natural-language
proof spells out equality of the additive closure of fraction relations with their
module span and naturality of the degree-zero comparison. No change record is needed:
there is no change to an existing statement, definition or public import.

## Second reading by M1

1. I compared the delivered item module with the repository version. The theorem
`invertS_cohomology` has the identical signature and visibility; only its proof and
proof-only imports changed. The two new module interfaces are new declarations and do
not alter an existing declaration.

2. I compiled all three delivered modules with `lcompile.py`; each completed without
errors or warnings. The only remaining `sorry` is the explicitly named theorem
`affineOpen_cohomology_localization_zero`. No definitions contain `sorry`, and the
proved declarations use only the permitted imported axioms (the remaining base theorem
is the documented open hole).

3. I checked the new statements against the degree-zero and affine-open cases of
Stacks 09MR, 01PW, and 01E1. The degree-zero theorem is exactly the ambient affine-open
comparison needed by the induction predicate; the all-degree theorem adds only the
positive-degree vanishing argument. Empty opens, zero sections, and degree zero were
checked as edge cases. Neither statement duplicates an existing declaration found by
source search.

4. The proofs follow the shortest available route: affine degree zero, affine
vanishing for positive degrees, then the existing gluing and quasi-compact-open
induction declarations. The removed affine-case and tensor-product imports are no
longer used, and the DAG proof/proof_deps entries match the actual proof. The unit route
through affine comparison, gluing, and induction is preserved.

5. The node records agree with the Lean statements and proof dependencies, including
the split degree-zero node and its source/docstring. The delivery adds one documented
lower hole while closing the original target hole, so this is recorded as a
decomposition with net zero holes.

Changed during second reading: added this review record only; no Lean statements or
proofs required repair.
