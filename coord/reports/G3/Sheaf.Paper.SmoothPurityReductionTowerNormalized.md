## What changed

Decomposed AlgebraicGeometry.ProEtale.sp_reduction_tower_normalized into four strictly
separate steps: strict descent in the fixed tower presentation; invertibility of the
specified reduction adjuncts; integral and finite-level Tor intervals; and finite-level
constructible cohomology. Their source and complete proofs in words are in their own
modules and nodes. This follows the existing DAG's construction, normalization, Tor
comparison, and finite-matrix/Postnikov route.

The final theorem explicitly constructs the commutative coefficient-ring comparison
from spIntegralAbComparison, including its underlying-map normalization. The private
ringPresheafMon_eq and liftSectionRingIso proofs are adapted from the already-proved
helpers in IntegralCriterionReductions, without importing that large theorem module.
It then assembles every SpReductionTower field. For constructibility it chooses a finite
Tor interval, widens its lower endpoint to min(a,b), and uses the same ordered interval
for all finite-level and uniform tower bounds. The arbitrary-interval conclusion is
retained separately.

The 18 original data declarations moved verbatim to SmoothPurityReductionTowerData,
publicly re-exported by the original item. All original public imports remain public.
No existing statement, definition body, coefficient construction, or universe changed.
Change record: coord/changes/G3-smooth-purity-reduction-data-relocation.md.

## Proved and sorry left

Original holes: 1. The complete body of
AlgebraicGeometry.ProEtale.sp_reduction_tower_normalized now compiles without a local
sorry, with its original signature. Its coefficient comparison and predicate assembly
are proved. This is a decomposition, not a proof of the complete mathematics:
1 upper hole is closed and 4 strictly smaller holes are added, for a net increase of 3.

The only remaining delivered holes are:

- AlgebraicGeometry.ProEtale.sp_reduction_tower_presentation_descent
  (lem-sp-reduction-tower-presentation-descent), in SmoothPurityReductionTowerDescent:
  ordinary and derived strict tensor descent only; no normalization or finiteness claim.
- AlgebraicGeometry.ProEtale.sp_reduction_tower_adjunct_normalization
  (lem-sp-reduction-tower-adjunct-normalization), in SmoothPurityReductionTowerAdjunct:
  comparison of D.reduction with scalar transitivity; no construction or finiteness.
- AlgebraicGeometry.ProEtale.sp_reduction_tower_tor_intervals
  (lem-sp-reduction-tower-tor-intervals), in SmoothPurityReductionTorIntervals:
  finite integral Tor amplitude and transfer of intervals; no normalization or
  finite-level constructibility.
- AlgebraicGeometry.ProEtale.sp_reduction_tower_level_constructibility
  (lem-sp-reduction-tower-level-constructibility), in SmoothPurityReductionLevelConstructible:
  constructible cohomology only; no Tor bound or normalization.

Every hole is the entire proof of a public named theorem. No data is defined by sorry
or by selection of an arbitrary witness of an unproved existence theorem.

Validation: the final six-module import-ordered lcompile.py run passed with no
warnings or errors: Data 36.5 s, LevelConstructible 35.1 s, TorIntervals 48.4 s,
Adjunct 30.1 s, Descent 36.1 s, and Normalized 59.0 s. A preceding individual compile
of the coefficient-comparison proof passed in 11.4 s, with only a subsequently fixed
long-line warning. The unchanged data block was checked byte-for-byte against the
shared original. DAG dependency unions, primary attachments, all new signatures and
parent dependency paths were checked; no new cycle reaches the parent. Two unchanged direct consumers also compiled against the overlay:
FieldScalarSystemData (32.8 s) and SmoothPurityCompletedTowerRoos (14.1 s). Their
sandbox source copies were removed after checking; neither is a delivery adaptation.
The delivery parser independently confirmed every relocated data declaration retains
its signature, body, visibility and attributes, and the final theorem signature agrees.

## No longer needed

No declaration or whole module is withdrawn. No module is claimed globally pruned:
the generic dependencies remain necessary for the four comparison steps and may remain
imported by other consumers. The following obsolete direct proof imports were removed
from the item; the data declarations compile from the retained public imports alone:

- Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
- Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
- Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
- Sheaf.Paper.ProEtaleConstructibleSheaf
- Sheaf.Paper.SmoothPurityCoefficientTowersAbelian
- Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat
- Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
- Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
- WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
- Sheaf.Paper.CompletedConstantSheafReduction
- WeilConjectures.ConstructibleSheaf.Refinement
- Sheaf.CategoryTheory.FiniteTypeLocallyConstantSerre
- Sheaf.Paper.ProjectionMateExact
- Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
- Sheaf.Paper.KFlatRingedToposPullback
- Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
- Sheaf.CategoryTheory.SitePullbackAbelianExact
- Sheaf.Paper.CondensedConstantConstructibility
- Sheaf.Paper.SmoothPurityCoefficientTowers
- Sheaf.Paper.LocalizingClosureCtfEqualsBc

The split statement files also omit unused proof-only imports of
StrictCoefficientTensorDescent, SuccessiveDerivedQuotientNormalization,
LocalizingClosureCtfEqualsBc, SiteDerivedTensorRestriction,
StratifiedReductionPostnikovComparison, IntegralLocalModelFiniteMatrixReduction,
PullbackFiniteConstantLocalModel and ConstructibleSheaf.Refinement. Their statements
compile using only the shared data module. These are postponed proof dependencies,
retained explicitly in the DAG rather than being claimed as mathematically pruned.

The original direct proof dependencies are now assigned to the four step nodes rather
than silently dropped. In particular strictCoefficientTensorDescent is retained for
construction, successive_derived_quotient_normalization for the actual adjuncts,
localizingClosure_ctf_equals_bc and siteDerivedTensorRestriction for Tor bounds, and
finite matrix reduction, common refinement, pullback of local models and stratified
Postnikov comparison for constructibility. The final proof adds no bypass of the unit:
its realized route is empty and its defining predicates are still used verbatim.

## Where the brief, the DAG or earlier work was wrong

The existing generic declarations use different presentations: strict tensor descent
uses SemilinearSections.Systems, whereas the item uses the chosen D.equivalence;
its generic computation clause starts with flat-term K-flat representatives, whereas
the item asks for every K-flat representative; scalar transitivity must be identified
with the actual D.reduction adjunct; and matrix/Postnikov models must be transported
to the internalized finite-constant-model constructibility convention. These are real
remaining comparisons, not missing or unsupported dependencies. The existing plan
remains mathematically applicable and is preserved in the new nodes.

Edge cases checked in the step statements and proofs in words: zero complexes, empty
schemes, n=0 representing exponent one, equal transition indices, unbounded complexes
in the construction and normalization, and nonflat quotient maps. Only the last two
finiteness steps assume qcqs. The Tor bounds retain the ordered-interval hypothesis;
the final assembly explicitly orders the chosen existential interval.

## New nodes

- def-sp-reduction-tower-data: the original 18 definitions, including SpReductionTower,
  relocated without changes; zero holes and no new mathematical notion.
- lem-sp-reduction-tower-presentation-descent: transport of existing generic descent
  and scalar models to the fixed integral coefficient and tower presentations.
- lem-sp-reduction-tower-adjunct-normalization: identification of actual D.reduction
  with the invertible successive scalar-extension comparison.
- lem-sp-reduction-tower-tor-intervals: integral finite Tor amplitude and the scalar
  restriction comparison for every finite-level interval.
- lem-sp-reduction-tower-level-constructibility: coefficient-preserving transport of
  finite matrix and Postnikov models to constructible finite-level homology.

All nodes cite the existing source and dependencies. LeanSearch, LeanFinder/Loogle,
Mathlib grep, and local Sheaf/source/blueprint searches found the generic ingredients
but no theorem for these specific presentation comparisons. The four statement nodes
do not assert the original theorem under another name: each omits independent required
parts, and the final proof performs their real combination.

## Second reading by G3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
