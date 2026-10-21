## What changed

Filled `CategoryTheory.RingedDerivedComparisons.compositionCore_exists` in
`Sheaf.SixFunctors.RingedDerivedCompositionComparison`. Public statements and definitions
are unchanged. All added helpers are private and proved. The ordinary module comparison is
constructed from the geometric right-adjoint mate: generalized scalar-linear combinations
show it is a module isomorphism, and the normalized Hom formulas give scalar insertion.
The existing derived ringed-square comparison, applied with an identity edge, gives the
composition comparison. Tensor compatibility descends from resolving representatives;
unit compatibility follows by cancellation from the strong monoidal unit laws. The right
mate formula follows from canonical Hom formulas, extended along K-injective resolutions,
and a K-flat resolution of the ordinary direct-image complex.

Validation: the complete module compiled with `lcompile.py` in 22.6 seconds.

Updated the existing node's proof, proof dependencies and proof origin to this route.
No new modules, public declarations, interfaces or nodes are introduced.

## Proved and sorry left

Closed the single original hole in
`CategoryTheory.RingedDerivedComparisons.compositionCore_exists`
(node `lem-sfb-ringed-derived-composition-comparison`). Holes closed: 1. Holes added: 0.
No `sorry` remains in the item, and no statements have been split off. The proof uses
existing declared results, including the identity comparison and tensor-lift existence
results, as permitted by stage 3; this does not claim their remaining proofs are closed.

## No longer needed

The direct proof no longer uses these planned dependencies:

- `lem-pur-cochain-pullback-tensor-coherence`
  (`Sheaf.SecSmoothPurity.CochainPullbackTensorCoherence`): the existing square tensor
  compatibility supplies the representative tensor equation.
- `lem-weil-pbc-ringed-topoi-derived-pullback`
  (`Sheaf.Paper.RingedTopoiDerivedPullbackIndependent`) and
  `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`
  (`Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`): the supplied lifts already
  record their alpha and tensor comparisons; square descent uses those interfaces.
- `lem-weil-pbc-ringed-topoi-derived-pushforward-composition`
  (`Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition`): kappa is the adjunction
  mate directly, and its formula is proved by transposing and resolving its source.
- `lem-weil-pbc-geometric-module-transport`
  (`Sheaf.CategoryTheory.GeometricModuleTransport`): the ordinary comparison is constructed
  here using generalized scalar-linear combinations and normalized adjunctions.
- `lem-pc-right-fraction-representation` and
  `lem-weil-pbc-localization-universal-property`: the model equality is tested after one
  explicit K-flat resolution; tensor natural transformations descend by the existing
  resolving-subcategory theorem.

Removed proof imports: `Sheaf.SecSmoothPurity.CochainPullbackTensorCoherence` and
`Mathlib.Algebra.Homology.DerivedCategory.Fractions`. The extra
`Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses` proof import was unnecessary:
the small-site theorem already exposed by the data module suffices.

These are removals of direct planned uses only. Several remain needed transitively by
other existing declarations; no source-library declaration or module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

No false statement was found. The original DAG route was longer than necessary for the
right-mate formula: its universal derived pushforward-composition argument can be replaced
by canonical Hom formulas and cancellation after a K-flat resolution. The tensor and
representative parts can reuse the already declared ringed-square comparison with an
identity edge. The blueprint unit's route and statement are retained.

Preflight initially flagged a global monoidal-namespace `open` command. It was removed;
namespace openings now scope individually to private helpers. The source interface check
then reports no interface changes, so no change record or consumer adaptation is needed.

## Second reading by M5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
