## What changed

Proved `AlgebraicGeometry.Etale.homComparisonAffineInputs` in
`Sheaf.Paper.HomComparisonAffineInputs`, with its entire signature unchanged.
Added six proved private helpers for bounded-flat pullback, homology vanishing,
the constructibility encoding conversion, bounded-constructible pullback,
the finite affine cover, and the explicitly reindexed stratification pullback.
The finite cover uses `Fin 0` for an empty scheme. The stratification indexes
exactly the nonempty fibre products and gives the required literal domain
equalities, immersion HEqs, preimage strata and finite locally constant sheaves.
The model isomorphism is exactly the prescribed composite for every input e.

Used the already proved general source etale flat-model equivalence instead
of its finite-coefficient wrapper, and the already proved source flat-pullback
and exact-functor cohomology APIs. Updated the existing node's proof,
proof_deps and proof_origin to describe this implementation. No declaration,
definition or node statement changed; no consumer adaptation was needed.
A direct-import search found no current Lean importer of the assigned module.
The DAG parents are preserved; the item is proved, not withdrawn.

The complete module compiled through lcompile.py after removing unused
imports (9.9 seconds in the last development check). All lines have at most
100 characters. The delivery tool performs the final compile and axiom check.

## Proved and sorry left

Closed 1 hole: `AlgebraicGeometry.Etale.homComparisonAffineInputs`
(node `lem-sf-hom-comparison-affine-inputs`).
Added 0 holes. There are 0 remaining sorries in the delivered module.
All six private helpers are proved. This is a complete proof, not a decomposition.

## No longer needed

Removed these direct imports:

- `Mathlib.AlgebraicGeometry.Morphisms.Proper`
- `Sheaf.Paper.FiniteCoefficientFlatModel`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`
- `Sheaf.AlgebraicGeometry.PullbackConstantModule`
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`
- `Mathlib.AlgebraicGeometry.Sites.MorphismProperty`
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`
- `Mathlib.Algebra.Homology.ShortComplex.PreservesHomology`
- `Sheaf.AlgebraicGeometry.EtaleInverseImageCompositionModuleLinear`
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback`
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`
- `WeilConjectures.AlgebraicGeometry.FiniteLocallyConstantModuleValues`

Replaced the public Proper import by Separated and the public specialized
FiniteCoefficientFlatModel import by the source Derived.Finiteness.FlatModel.
The remaining original public imports provide notions in the statement;
the added source imports are private proof imports.

The proof no longer directly needs these planned dependency nodes:

- `lem-kun-pullback-constant`
- `lem-sf-flat-model`
- `lem-weil-pbc-etale-covering-base-change`
- `lem-weil-pbc-etale-inverse-image-restriction`
- `lem-weil-pbc-inverse-image-composition-module-linear`
- `lem-weil-pbc-open-immersion-etale`
- `lem-weil-pbc-ringed-topos-flat-module-pullback`
- `prop-weil-pbc-inverse-image-modules-exact`

The source categorical ModuleCat-valued pullback already supplies exactness,
module-linear composition, locally constant pullback, and flatness via geometric
stalks. There is no need to transport through the separate SheafOfModules
constant-ring encoding. The general source flat-model theorem also makes
residue-field invertibility instances unnecessary for this proof. The old
finite-coefficient wrapper's node stays as a statement dependency because
statement dependencies were not changed. These are local dependency/import
prunings; no module is withdrawn and no upstream declaration is removed.

## Where the brief, the DAG or earlier work was wrong

The plan was mathematically sufficient but used a longer encoding route than
the available proved source library. In particular, the source general etale
flat-model equivalence needs no invertibility instance, and the categorical
module-valued inverse-image compositor is already linear. The source
Stratification.pullback alone retains empty strata and uses a different
stratification structure; the private construction explicitly restricts its
index to nonempty fibre products and proves the covering property, so it
meets the stronger displayed conclusion for the project's finite locally
closed stratifications. No disputed statement or unit-route change occurred.

## Second reading by J8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
