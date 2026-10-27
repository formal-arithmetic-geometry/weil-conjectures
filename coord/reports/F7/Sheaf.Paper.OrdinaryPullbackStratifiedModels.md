## What changed

Filled five existing proofs in `Sheaf.Paper.OrdinaryPullbackStratifiedModels`, preserving
all public signatures, public imports and definition bodies.

The main theorem constructs the pullback stratification explicitly, indexed by exactly the
nonempty pullback schemes. Coverage follows by lifting a point through the pullback range
formula. The base-change site functor transports each covering sieve; its terminal comparison
identifies the resulting family with the family in the statement. The final local map is the
composite of the original localExchange, the given chart isomorphism under ordinary derived
pullback, and the invertible counit/model composite.

For the perfect-model counit, a proved private object isomorphism identifies the original
chosen scalar-extension model with the explicit finite-projective dependency's model. The
isomorphism is the published tensor object specification followed by sheafification of an
identity-component presheaf isomorphism; tensor induction checks restriction compatibility.
Flatness transfers across it. The given upper bound transfers through the additive functor,
so the independent-universe bounded-flat criterion supplies K-flatness. The existing ordinary
computation-counit theorem then applies. No coefficient-map flatness or completeness is used.

Coefficient composition is checked first on finite constant direct-image maps, using the
proved calculation in CompletedCoefficientRingedCoherence and forgetting commutativity.
The projection specification and uniqueness give completed direct-image composition. The
adjunction-mate equation yields the specified inverse-image compositor; adjunction naturality
also gives every finite projection. A small generic categorical projection lemma keeps
this calculation independent of unfolding the concrete site functors. Scalar additivity and
the tensor object specification come from the existing constant-realization and derived-change-of-rings APIs.

Validation: the complete item compiled through lcompile.py without errors or warnings
in 21.2 seconds, below the unchanged 60-second limit. The sandbox contains one Lean
module, with five remaining named theorem holes and no added holes.

Updated the item's DAG proof and proof dependencies to describe these arguments.
A declaration-local unused-variable linter option preserves the original `L` index binder
without a warning; its record is
`coord/changes/F7-ordinary-stratified-models-linter-scope.md`. No public type changes. No other
existing module or node changed, and no public helper or new mathematical statement was added.

Searches: msearch Loogle for Functor.Additive/comp, LeanFinder for base change of finite locally
closed stratifications and pro-etale covers, and msearch grep plus local rg. Searches located
additive composition and generic geometric tools; the existing finite-projective model file
already proves the necessary flatness. The main geometric construction also handles zero
strata and the empty source: a point over an original stratum certifies that its pullback index
survives deletion. The scalar-model transport works for zero modules and rank-zero summands.

## Proved and sorry left

Closed 5 of the original 10 holes; added 0 holes. These are completed proofs, not a
decomposition. Names below are in namespace `WeilConjectures.OrdinaryStratifiedModels`.

Closed:

- `coefficientMap_comp`.
- `modelModule_additive`.
- `modelModule_obj`.
- `perfectModelPullback`.
- `ordinaryPullbackStratifiedModels`.

The five existing named theorem holes remain, all attached to
`lem-tw-ordinary-pullback-stratified-models` with their original source and proof docstrings:

- `modelPullback_existsUnique`.
- `moduleSquare_existsUnique`.
- `derivedSquare_existsUnique`.
- `immersionExact`.
- `weaklyEtaleExact`.

The normalized model isomorphism and square-comparison definitions still depend on those
existing statements. In particular, closing the main theorem does not assert that its full
axiom closure is sorry-free. No definition contains a hole.

## No longer needed

Removed the following proof imports from the item:

- `WeilConjectures.ConstructibleSheaf.Pullback`.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingComposition`.
- `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`.
- `Sheaf.Paper.LocalizeRingedSiteMorphismGeneral`.
- `Sheaf.SixFunctors.RingedDerivedMonoidalComparisons`.
- `Sheaf.Paper.SfImmersionCompletedPullbackComparison`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`.
- `Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat`.
- `Sheaf.Paper.RingedTopoiDerivedPullback`.
- `Sheaf.CategoryTheory.SiteRepresentableAlgebraicPullback`.

The geometric proof uses direct preimages and Mathlib's pullback range formula, so
`lemma-constructible-pullback-stratification` is no longer a direct proof dependency.
`lem-weil-pbc-weakly-etale-composition-base-change` and
`lem-galois-fpqc-covering-base-change` are encapsulated by the already existing
`proEtaleBaseChangeCoverPreserving`; the proof no longer invokes them separately.
Removed exactly those three obsolete approvals from the item's existing tool_uses list.
The old bounded-above flat module is replaced by the independent-universe bounded-flat API.
The other hints remain relevant to the still-open canonical comparison statements, but need
no standalone import in this partial proof. No module is withdrawn and no upstream declaration
is removed; many removed direct imports remain transitively reachable elsewhere.

## Where the brief, the DAG or earlier work was wrong

The source-library Stratification.pullback uses a different stratification record, keeps empty
strata, and orders its fibre product oppositely. It is not a direct inhabitant of the main
conclusion. The explicit finite subtype construction supplies the required bijection and the
literal pullback.fst-compatible domain isomorphisms without changing the statement.

The finite-projective dependency uses an explicit universe-aware tensor functor, whereas this
item uses the selected functor from derivedChangeOfRingsIndependentCoefficients. They cannot
be substituted merely by naming them alike: the private object isomorphism checks the tensor
restriction maps and is used solely to transfer flatness. The general derived chart dependency
likewise has a different comparison record, so its existence is not silently identified with
this item's generator-normalized chosen square. Those existing canonical-comparison holes are
retained honestly.

Generic tools newly recorded in proof_deps are
`lem-weil-pbc-completed-constant-sheaf-reduction`, `lem-pur-derived-change-of-rings`, and
`lem-weil-pbc-independent-bounded-flat-kflat`. They supply constant additivity, the prescribed
ordinary tensor objects, and bounded-flat K-flatness respectively. They preserve the unit's
route; no new tool_uses approval is written by the worker.

## Second reading by F7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
