## What changed

Proved `AlgebraicGeometry.Etale.stratified_cohomology_slice_models` in
`Sheaf.Paper.StratifiedCohomologySliceModels`, with its original signature and public
imports unchanged. Added the proved private helper `finiteSliceModels`.

The common-stratification induction uses the existing finite-value/finite-stalk
constructibility comparison, `Stratification.inter`, and preservation under refinement.
Exact derived pullback gives the cohomology comparison and vanishing. For every etale
object, base change a locally constant cover, lift its index type to the coefficient
universe, obtain finite constant models on its members, and lift their isomorphisms
through the actual slice-site equivalence. All isomorphisms are in `ModuleCat B`.

Added private proof imports of
`WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison`,
`WeilConjectures.ConstructibleSheaf.OpenClosed`,
`WeilConjectures.ConstructibleSheaf.FiniteConstantModel`,
`Mathlib.Data.Int.Interval`, and `Mathlib.RingTheory.Finiteness.Cardinality`.
Retained the private import of `WeilConjectures.ConstructibleSheaf.Refinement`.
Updated only `proof`, `proof_deps`, and `proof_origin` of the item's existing DAG node.
No other module, declaration interface, or node attachment changes.

Validation: the complete file compiled without errors or warnings through `lcompile.py`
(12.1 seconds on the final proof/import check). `#print axioms` reports exactly
`propext`, `Classical.choice`, and `Quot.sound` for the public theorem. The diagnostic
command was removed after checking. A preflight complaint about an added namespace-opening
command was repaired by fully qualifying helper names; no public command change remains. The new dependency edges introduce no DAG cycle.
The public theorem's signature was compared verbatim with the current source.

The proof uses no nonempty-scheme or nonempty-stratum assumption: finite constant model
extraction handles empty schemes; the pulled-back cover is jointly surjective even when
its target is empty. Outside the finite interval the zero-sheaf case supplies finite
local constancy. Singleton intervals, empty fibre products, and the zero coefficient ring
require no special restriction. The unit's realized statement and steps are unchanged.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Etale.stratified_cohomology_slice_models`
(node `lem-weil-pbc-stratified-cohomology-slice-models`).

Original holes: 1. Closed: 1. Added: 0. Split off: 0. Remaining: 0.
The private helper is completely proved. The public theorem's transitive axioms are clean.

## No longer needed

Removed these direct private proof imports:

- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`
- `Sheaf.CategoryTheory.ConstantLeftModuleInverseImage`
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`
- `Sheaf.AlgebraicGeometry.EtaleInverseImageCompositionModuleLinearCore`
- `Mathlib.AlgebraicGeometry.Sites.MorphismProperty`
- `Sheaf.SixFunctors.GeometricInverseImageConstantModule`
- `Sheaf.CategoryTheory.ExactDerivedCohomologyCoherence`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtaleOver`

Removed direct proof-dependency edges to
`prop-weil-pbc-inverse-image-modules-exact`,
`lem-pe-constant-left-module-inverse-image`,
`lem-weil-pbc-etale-inverse-image-restriction`,
`lem-weil-pbc-inverse-image-composition-module-linear-core`, and
`lem-sfb-geometric-inverse-image-constant-module`: the adopted generic ModuleCat-valued
pullback, compositor, constant-sheaf comparison, and slice equivalence already provide
the required linear maps. Removed `lem-pur-exact-derived-cohomology-coherence`: only
its existing ordinary cohomology comparison is needed, supplied by the proved node
`lem-weil-pbc-exact-functor-bounded-below`; the additional compositor coherence is unused.

Removed proof-only edges to `def-weil-pbc-etale-constructible-sheaf`,
`def-pur-localized-ringed-site`, and `def-weil-pbc-etale-site`; these remain statement
dependencies. Finite constructibility is converted using the existing comparison theorem.
The varying-ring `SheafOfModules.overFunctor` interface is unnecessary for the fixed-ring
module-valued sheaves in this statement.

The localization node `lem-weil-pbc-etale-site-localization-open` and covering base-change
node are retained: their declarations are available through the proved source modules.
Some removed direct import modules are still imported transitively by those source
modules. No module is withdrawn and no whole-library pruning count is claimed.

## Where the brief, the DAG or earlier work was wrong

The existing proof plan calls for substantially more compatibility theory than this
existence statement needs. The adopted source interfaces already give module-valued
pullbacks, finite local constancy under refinement, and finite constant models; their
complete proofs suffice here. The stronger exact-derived compositor-coherence theorem
is unnecessary. Likewise the cover datum already has a small index type, so `ULift`
suffices; choosing a member above every point to shrink a larger family is unnecessary.

Sources read: `literature/stacks-project/etale-cohomology.tex`,
`lemma-constructible-quasi-compact-quasi-separated` (095E),
`lemma-constructible-abelian` (03RZ), and `lemma-pullback-locally-constant` (095A);
`literature/stacks-project/derived.tex`, `lemma-right-derived-exact-functor` (015F).
Searches through `msearch.py` included LeanFinder for a common finite stratification,
Loogle for sheaf homology, and grep for stratified/constructible cohomology. None returned
the requested theorem; direct source-library searches found the interfaces used above.
The module named in the historical source citation,
`FiniteFieldStratifiedPerfectModels.lean`, is absent from the current source tree; the
present proof uses the current available declarations and preserves the assigned item.

## Second reading by K1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
