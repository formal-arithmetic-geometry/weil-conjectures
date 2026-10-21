## What changed

Proved `AlgebraicGeometry.Scheme.perfect_strata_uniform_reductions` with its original
signature and public imports unchanged. Added two fully proved public lemmas in new
modules: `perfect_local_reduction_models` and `perfect_chart_tensor_comparison`.
Updated the main node's proof route and added matching nodes for the new lemmas.

The chart lemma transports the local model through geometric pullback and scalar
extension using adjunction uniqueness and the derived slice equivalence. The quotient
normalization follows from the completed-ring limit projections. K-flat constant
complexes and the existing constant tensor comparison compute every finite reduction.
The local lemma takes homology, proves finiteness through finite terms, cycles and
quotients, and supplies one interval for the completed model and all reductions.

The main proof chooses one finite quasi-compact sieve refinement of each stratum cover,
before choosing the reduction index. Sums of absolute endpoints give common bounds,
including [0,0] for an empty refinement. Cover descent and locally closed-stratum
abelian detection prove global vanishing. The intrinsic coefficient finite-sieve and
constructibility equivalences give constructibility directly on the original covers.

Validation: all three modules compiled cleanly through `lcompile.py --all`; no local
Lean or library build was run. Empty schemes/charts, zero complexes, zero quotients,
I=0 and I=A, and both signs of the support interval were checked in the argument.
No assumption requires a nonempty chart, a nonzero ring or a nonempty finite refinement.
The first delivery preflight requested LeanSearch as a separate search kind; a real
LeanSearch run was added to both new-node records before retrying.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.perfect_strata_uniform_reductions`
(`lem-weil-pbc-perfect-strata-uniform-reductions`).

Added zero holes. Both new theorems, `perfect_local_reduction_models`
(`lem-weil-pbc-perfect-local-reduction-models`) and `perfect_chart_tensor_comparison`
(`lem-weil-pbc-perfect-chart-tensor-comparison`), have complete proofs. There is no
`sorry` in any delivered Lean file. This closes one item hole, rather than moving it
into a decomposition. Existing imported library declarations remain as they were.

## No longer needed

Removed these original proof imports from the assigned module:

- `Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat`
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`
- `Sheaf.CategoryTheory.FiniteTypeConstantExact`
- `Sheaf.AlgebraicGeometry.NoetherianStratumDetection`
- `Sheaf.RingTheory.IndEtaleStability`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale`
- `Sheaf.AlgebraicGeometry.ProEtaleModuleStalkFunctor`
- `Sheaf.AlgebraicGeometry.ProEtaleConstantSheafStalk`

The revised main proof no longer calls the following old planned dependencies directly:

- `def-pc-perfect-ring-complex`
- `def-weil-pbc-projective-module`
- `def-pur-sheaf-tensor-product`
- `lem-pc-bounded-above-flat-kflat-site`
- `lem-pur-derived-change-of-rings`
- `lem-weil-pbc-stratum-completion-unit-restriction`
- `lem-weil-pbc-finite-type-constant-exact`
- `def-weil-pbc-adic-coefficient-datum`
- `lem-sfb-stratified-local-cohomological-bounds`
- `lem-weil-pbc-noetherian-stratum-detection`
- `def-weil-pbc-proetale-covering`
- `lem-weil-pbc-ind-etale-stability`
- `lem-weil-pbc-noetherian-scheme-closed-subsets-minimal`
- `lem-weil-pbc-qcqs-morphism-permanence`
- `def-weil-constructible-subset`
- `def-weil-proetale-constructible-sheaf`
- `def-weil-pbc-fpqc-covering`
- `lem-fix-weakly-etale-algclosed-section`
- `def-weil-proetale-geometric-stalk`
- `lem-weil-proetale-constant-sheaf-stalk`

The perfect representative, flatness and scalar-extension computations now occur in
the proved local/chart lemmas and use the existing independent-coefficient K-flat and
scalar-adjunction APIs. Constants commute with homology through their existing exact
functor API. Finite covering sieves and abelian stratum detection replace the older
stratified-bounds/detection route. Intrinsic finite coefficient constructibility
replaces the separate geometric-stalk lifting argument. Definitions still occur in
unchanged statement dependencies when needed; this list is not a withdrawal request.
No existing module or declaration is deleted, including those in WeilConjectures.
Global reachability is left to the maintainer's ledger.

Withdrew the five obsolete main-node tool approvals, without adding or reordering any:
`lem-pc-bounded-above-flat-kflat-site`, `lem-pur-derived-change-of-rings`,
`lem-sfb-stratified-local-cohomological-bounds`,
`lem-fix-weakly-etale-algclosed-section`, and
`lem-weil-proetale-constant-sheaf-stalk`.

## Where the brief, the DAG or earlier work was wrong

No statement was found false, and no existing signature or definition changed.
The seven-step DAG plan is longer than necessary with the current coefficient APIs:
the intrinsic coefficient criterion already turns finite constant models on covering
sieves into constructibility, so the separate geometric-stalk argument is redundant.
`ProEt.qc_finite_cover` already supplies a finite refinement factoring through original
cover members; the proof needs no new open-immersion/qcqs permanence argument.

The slice module equivalence proof only requires that the chart is weakly etale.
Its existing implementation for open immersions uses no open-immersion assumption;
the private helper records that same proof for every pro-etale chart. All such helpers
are fully proved. The finite-cover helper is read from `ProEtaleTorLocalGlobal`, whose
broader Tor-amplitude theorem is not invoked. These existing proved helpers avoid
introducing additional unproved mathematical dependencies.

## New nodes

`lem-weil-pbc-perfect-chart-tensor-comparison`, module
`Sheaf.Paper.PerfectChartTensorComparison`: proves termwise finite reduction on one
original chart from a bounded finite-projective complex and its local-model isomorphism.
This is the scalar compatibility calculation of the source, strictly below uniform
bounds or constructibility. Its main ingredients are the existing geometric/scalar
adjunctions, weakly etale slice localization, ring-isomorphism scalar extension,
bounded-flat independent-coefficient K-flatness, and constant scalar realization.

`lem-weil-pbc-perfect-local-reduction-models`, module
`Sheaf.Paper.PerfectLocalReductionModels`: chooses a perfect representative and derives
local completed/reduced vanishing and finite constant homology models on one chart.
It has no finite stratification, global descent or constructibility conclusion.
Both new nodes are proved in this delivery. The proper-base-change unit route stays
unchanged. There are no change records because no existing statement or definition
was repaired, and there are no forced adaptations.

## Second reading by B2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
