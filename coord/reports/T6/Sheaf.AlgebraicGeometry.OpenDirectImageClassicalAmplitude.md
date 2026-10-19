## What changed

Proved `AlgebraicGeometry.ProEtale.openDirectImage_classical_amplitude` with its
original signature, including arbitrary finite associative rings. Only the item module
and its DAG proof route change. Private helpers establish exact coefficient forgetting,
acyclicity of forgotten injective module sheaves on every étale object, and the derived
module/abelian direct-image comparison. The finite coefficient realization transports
injectivity to the ringed-site module category. The existing universe-correct Čech
cocycle lifting theorem, Čech-complex comparison and vanishing criterion give the
required acyclicity. This avoids assuming that forgetting preserves injectives.

The main proof extracts the least natural bound from the defining ENat infimum,
uses additive torsion of modules over a finite ring, and reflects zero by the faithful
forgetful functor. The canonical qcqs comparison transfers the result to pro-étale
sheaves; exactness is explicitly obtained from `siteComparison_finiteLevel`, retaining
the unit-route import and declaration. For bounded complexes, `DerivedCategory.isLE_obj_of_isLE` performs the finite
truncation induction already proved in the source library; the derived lower-bound
API handles degrees below a. Shift and triangulated structures are transported along
`rightDerivedFunctorIsoKInjectives`. This keeps the unit's route: the Stacks 0F10 étale
bound followed by canonical étale/pro-étale comparison.

Existing public declarations and definitions retain their signatures and meaning.
All new helper declarations are private and proved. Elaboration is sequential, with
the ordinary compiler time and heartbeat limits. Profiling options occur only in the
scratchpad, outside the delivery.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.ProEtale.openDirectImage_classical_amplitude`
(node `det-geo-open-finiteness-ii-amplitude`). Added 0 holes; split off 0 statements.
No `sorry` remains in the item module. Its proof uses the existing stated library
results, including the canonical comparison theorem. This reports the local hole
closure, not a claim that all imported results are independently axiom-free.

The complete retained proof compiled cleanly against the current server library with
`lcompile.py` in 30.4 seconds (exit 0, no warnings) in this resumed session. Final
consumer and metadata checks are performed by the delivery dry run.

## No longer needed

Removed imports (the first two were public; the others were proof imports):

- `Sheaf.AlgebraicGeometry.ProEtaleSmallModelComparison`: no transported small-model
  construction is used; the proof uses the original canonical comparison.
- `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`: uses the existing
  plus-derived functor and its compatibility with the ordinary derived functor.
- `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian`: category
  instances are already available through the statement imports.
- `WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful`: proves exactness
  of the fixed-ring forgetting functor directly from Mathlib adjunctions.
- `Sheaf.CategoryTheory.ModuleAbelianEvaluationComparison`: replaces its common-universe
  interface with the existing universe-correct Čech cocycle theorem.
- `WeilConjectures.CategoryTheory.Abelian.RightDerived.LongExactSequence`: uses the
  plus-derived acyclic base-change criterion instead of constructing a new long exact
  sequence or acyclic resolution comparison.
- `WeilConjectures.CategoryTheory.TruncationHypercohomology`: finite truncation
  induction gives the interval bound directly, without a spectral sequence.
- `Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses`: the coefficient
  categories already have the requisite instances through the statement imports.

Removed from the node's proof dependencies (and withdrawn their obsolete tool-use
entries where present): `lem-weil-pbc-noetherian-open-subscheme-noetherian`
(the direct compact-source/quasi-separated-target API suffices),
`lem-weil-pbc-ring-sheaves-grothendieck`,
`lem-weil-pbc-grothendieck-functorial-injective-embedding`,
`lem-weil-pbc-dplus-injective-representative` (the derived-functor API packages
resolutions), `def-sfb-right-derived-functor`,
`lem-weil-pbc-module-sheaves-colimits-forgetful`,
`lem-weil-pbc-ringed-site-module-abelian-evaluation-comparison`,
`lemma-weil-pbc-leray-acyclicity`,
and `thm-sp-truncation-e2`, for the reasons above. These are dependencies this proof
no longer needs; other parents may still need them. No module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The existing general direct-image coefficient comparison assumes `CommRing`, while
this item assumes only `Ring`. The private comparison proves the finite associative-ring
case from already declared ingredients instead of narrowing the statement. The
common-universe ringed-site evaluation interface cannot directly handle the small étale
site with coefficient universe u+1; the existing maximum-universe Čech lifting theorem
fits. The DAG's truncation spectral sequence is unnecessary: the source library already
proves finite truncation dévissage with exactly the needed upper bound.

Earlier attempts encountered compiler-service failures and timeouts. The retained
scratch proof also needed explicit transported shift and triangulated structures at the
last amplitude step. Those are now supplied, and successful compiler responses have
verified the resulting proof. Temporary development options and an unused topology
calculation were removed. No target statement, mathematical definition, or coefficient
hypothesis changed. No new nodes or forced adaptations are needed.

The resumed packet lacked the import-change record named by the retained report.
Restored `coord/changes/T6-open-amplitude-imports.md` with the full consumer table.
The finite-level comparison module remains imported and supplies both exactness
instances explicitly in the cohomology-transfer argument.

## Second reading by T6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
