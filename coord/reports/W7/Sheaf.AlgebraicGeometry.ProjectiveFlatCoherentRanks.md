## What changed

Proved `AlgebraicGeometry.projectiveFlatCoherent_geometricCohomology_constructible` in
`Sheaf.AlgebraicGeometry.ProjectiveFlatCoherentRanks`, preserving its signature and all
public imports. The existing source-library theorem
`Scheme.Modules.finite_range_and_isConstructible_finrankH_geometricFibre` already supplies
finite range and constructible level sets. Its hypotheses follow from projectivity,
Noetherianity, and coherence. Two proved private helpers supply finite presentation of a
coherent module and the scalar-compatible comparison between module-valued cohomology and
`Scheme.Modules.H`. Uniqueness of left adjoints compares tensor pullback with ordinary
pullback. No definition or existing statement changed, and no consumer adaptation is needed.

Added six proof imports: `WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.GeometricFibreRank`,
`WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian`,
`WeilConjectures.AlgebraicGeometry.CoherentAffineSectionsFinite`,
`WeilConjectures.AlgebraicGeometry.QuasicoherentFiniteTypeAffine`,
`WeilConjectures.AlgebraicGeometry.ModuleCohomologySourceComparison`, and
`WeilConjectures.AlgebraicGeometry.ModuleCohomologyScalarEndomorphism`.

Updated the existing node's proof, proof dependencies, proof origin, and removed its obsolete
tool-use approvals. The unit record has no realized statement or steps for this node; the
shorter route specializes an existing implementation of the same blueprint result.

Validation: the entire delivered module compiled cleanly through `lcompile.py` in 9.2 s.
The argument chooses no point of the base and takes no maximum, so empty bases are included.
The additive comparison is made linear using naturality for scalar multiplication; no
unrelated field action is substituted. Degree zero and the zero coefficient module are
covered by the same comparison. The delivery tool performs the final declaration and axiom
checks.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.projectiveFlatCoherent_geometricCohomology_constructible`
(node `lem-fin-projective-flat-coherent-ranks`).

Added 0 holes; split off 0 statements. There are no remaining `sorry`s in the delivered
module and no new modules. Both private helpers are completely proved.

## No longer needed

Removed the following proof imports:

- `Sheaf.AlgebraicGeometry.PerfectComplex`
- `Sheaf.RingTheory.FiniteProjectiveStandardFreeCover`
- `Sheaf.AlgebraicGeometry.LocalizedPullbackPerfectModel`
- `Sheaf.AlgebraicGeometry.FiniteFreeComplexHomologyUpperSemicontinuous`
- `Sheaf.AlgebraicGeometry.ProjectiveNoetherianDirectImagePerfect`
- `Sheaf.AlgebraicGeometry.ProjectiveNoetherianPerfectBaseChange`
- `WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.RfPerfect`
- `WeilConjectures.AlgebraicGeometry.PQFCohomology`
- `WeilConjectures.AlgebraicGeometry.TensorPullback`
- `WeilConjectures.RingTheory.FiniteProjectiveStandardFreeCover`

The last two cohomology/pullback modules are already re-exported by the unchanged public
statement imports. The other direct imports serve the old reconstruction of finite perfect
models, which the existing geometric-fibre theorem makes unnecessary in this file.

Removed from this node's direct proof dependencies:
`lem-sc-affine-noetherian-underlying-space`, `lem-pc-projective-noetherian-rf-perfect`,
`def-pc-perfect-complex`, `lem-weil-pbc-finite-projective-standard-free-cover`,
`cor-pc-projective-noetherian-rf-perfect-base-change`,
`lem-pc-localized-pullback-perfect-model`, `pqf-def-cohomology`,
`lem-sc-finite-free-complex-homology-upper-semicontinuous`, and `def-weil-affine-spectrum`.
The unchanged statement imports and dependencies still provide its cohomology and spectrum
notation. The source-library implementation may use analogous perfect-model theory
transitively; this report claims removal of this item's direct dependencies, not that every
such module leaves the targets' complete import closure.

Removed the five old tool-use approvals for the direct perfectness, perfect base-change,
standard-free-cover, localized-model and finite-free-semicontinuity nodes, because this
proof no longer invokes those declarations directly.

## Where the brief, the DAG or earlier work was wrong

The earlier DAG plan predates the existing implementation in
`WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.GeometricFibreRank`, whose module
docstring explicitly names this same blueprint result. Its convention uses ordinary
pullback and Ext-based cohomology; the delivered proof supplies the required bridges to the
unchanged statement rather than assuming definitional equality. The retired Sheaf
perfectness/base-change wrappers are not needed. No mathematical statement was disputed.

## Second reading by W7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
