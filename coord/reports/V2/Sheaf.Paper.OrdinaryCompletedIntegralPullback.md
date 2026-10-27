## What changed

Prove ordinaryCompletedIntegralPullback by transporting stratified perfect models and
identifying the specified natural comparison with the intrinsic completion reflector unit
through the existing augmentation-normalized strict-model comparison. The ordinary functors, adjunctions,
quotient augmentation and comparison descent move to OrdinaryIntegralPullbackConstruction;
the original module publicly reexports them with their names and signatures unchanged.
ProperIntegralOrdinaryData imports the construction module; ProperIntegralStrictModelComparison
names that construction as a direct proof import; FiniteProjectiveModelPullback
redirects its proof-only import-all for two private constant-section helpers there.
This separates the construction from its constructible-isomorphism conclusion and permits
the construction-only coefficient comparison to be used without an import cycle.

## Proved and sorry left

The assigned module originally had one hole, closed by
WeilConjectures.ordinaryCompletedIntegralPullback. Holes closed: 1. Holes added: 0.
Sorries left in the item and new modules: none. The new
AlgebraicGeometry.Scheme.integralStratifiedPerfect_pullback is proved without sorry.
The final packet is checked through lcompile and deliver3. The constructor profiling
compile passed in 46.2 seconds after making the private counit component equation
explicitly unfold its locally irreducible definition. Temporary profiler options are removed
before delivery. The strict-model
module explicitly imports the new constructor module and is rebuilt with the packet,
so compiled dependency records follow the moved declarations.
The delivered import adaptation of
WeilConjectures.pbc_proper_integral_strict_model_comparison retains its one pre-existing
sorry (node lem-weil-pbc-proper-integral-strict-model-comparison); its statement and proof
are unchanged. This packet does not claim to prove that dependency. Likewise the existing
pbcActualCompletedPullback_tower and pbcActualCompleteInclusion_isRightAdjoint are used
as stated dependencies, not copied or reproved.

## No longer needed

The route does not use OrdinaryPullbackStratifiedModels or its finite projective
cochain conversion. Direct inverse image in the coefficient-datum presentation
transports each existing perfect scalar derived object and its local model.
That existing module and its declarations are retained, since other parents may need them.
The extraction is required for the dependency direction, not a timeout workaround.
No source-library declaration is removed or changed.

The final proof does not need the former direct proof imports
Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction,
Sheaf.Paper.RingedTopoiDerivedPullbackIndependent,
Sheaf.AlgebraicGeometry.ProEtaleAlgebraicInverseImage,
Sheaf.AlgebraicGeometry.ProEtaleToposFunctorialityInverseImage,
Sheaf.AlgebraicGeometry.ProEtaleModuleInverseImageCanonicalUnit,
Sheaf.Algebra.Category.ModuleCat.Sheaf.PullbackExistsOfUniverses,
Sheaf.Paper.IntegralAmbientOperationModels and Sheaf.Paper.IntegralOperationsWellDefined
at the theorem layer. Construction-only dependencies stay in the extracted module.
The old direct proof dependencies no longer used by the theorem are:
lem-pur-integral-ambient-operation-models,
lem-pur-ringed-site-module-pullback-exists-universes,
lem-tw-ordinary-pullback-stratified-models,
lem-weil-l-adic-extension-integers-dvr,
lem-weil-pbc-ringed-topoi-derived-pullback,
lem-weil-valued-dvr-finite-quotients, and prop-weil-pbc-koszul-reconstruction.
Several remain transitive dependencies of the unchanged constructors or existing tools;
this delivery does not claim to prune those modules from every target.

Obsolete top-level tool approvals removed from this theorem node (the underlying
constructor dependencies remain recorded on their own nodes):

- det-pe-topos-functoriality-inverse-image
- lem-pur-integral-operations-well-defined
- lem-sf-immersion-completed-pullback-comparison
- lem-sfb-ringed-derived-monoidal-comparisons
- lem-weil-l-adic-extension-integers-dvr
- lem-weil-pbc-left-exact-site-inverse-image-tensor
- lem-weil-pbc-ringed-derived-slice-localization
- lem-weil-pbc-ringed-topoi-derived-pullback
- lem-weil-pbc-ringed-topos-kflat-pullback
- lem-weil-valued-dvr-finite-quotients
- prop-weil-pbc-koszul-reconstruction
- prop-weil-pbc-proetale-constant-exact
- lem-pur-integral-ambient-operation-models

No module is withdrawn. The unused planned ordinary cochain-model interface and the
DVR/finite-quotient, direct Koszul reconstruction, immersion restriction and K-flat
pullback steps are replaced here by the datum chart equivalences, perfect-model
characterization, and existing unit-compatible strict-tower completion theorem.

## Where the brief, the DAG or earlier work was wrong

The ordinary constructors and the constructible-isomorphism conclusion shared a module.
Both OrdinaryPullbackStratifiedModels and ProperIntegralOrdinaryData imported that module
for its constructors. Importing their interfaces into its final proof caused a cycle.
The data and strict-comparison nodes also cited the final theorem node for construction-only
interfaces. Their references now name the construction, total-derived and comparison-descent
nodes; their mathematical assertions and Lean signatures do not change.

## New nodes

lem-tw-integral-local-model-pullback records direct transport of stratified perfect
local models in the coefficient-datum presentation, independently of any completion map.
It is a proved auxiliary result, not an unfinished split.
Change record: coord/changes/ordinary-integral-construction-extraction.md.

The strict-model comparison (lem-weil-pbc-proper-integral-strict-model-comparison),
completed-pullback reflector comparison (def-weil-pbc-completed-pullback),
completed-coefficient presentation equivalence, extension-zero chart transport and perfect-chart equivalence are
used as generic tools. The item's unit has no alternative presentation/reflector interface;
these tools do not replace its dual-stalk argument. No maintainer tool approval is added
or rewritten by this delivery.


The data and strict-comparison nodes had construction-only references to the final
ordinary pullback theorem node. These references now name the three earlier construction
nodes. Their statements retain exactly the same mathematical content. The complete citer
audit is recorded in each statement_change record: every citer holds because no Lean
signature or mathematical assertion changes.

## Second reading by V2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
