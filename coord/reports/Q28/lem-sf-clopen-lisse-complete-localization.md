## Worker report

The delivery states `WeilConjectures.sf_clopen_lisse_complete_localization` in
`Sheaf.Paper.SfClopenLisseCompleteLocalization`. Its proof is `sorry`; all helper
definitions contain actual constructions. The helper structures package the
coefficient comparisons and the compatibility assertions that belong to this node.
They are conclusions under an existential, not additional hypotheses.
The item statement, proof text and source are unchanged. The statement dependencies
name the definitions used; the three theorem nodes identified by the return are
retained only as proof dependencies, as the maintainer explicitly requested.

The node was read together with all its statement-dependency records, the full
signatures and docstrings of their declarations, the current blueprint context,
and the cited local Stacks sources. In particular the local-structure argument is
in `proetale.tex` (local-structure-constructible-complex, Tags 09C3/098F), the
contractible-cover argument supplies the splitting of the finite covering, and
`sites-cohomology.tex` Tag 0946 supplies evaluation exactness.

Hypothesis and clause correspondence:

| Node text | Lean rendering |
| --- | --- |
| Prime ell | Section binders `(l : ℕ) [Fact l.Prime]`. |
| Finite extension E/Q_l, valuation ring, quotients and residue field | `(E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]`; the recorded `Padic.coefficientExtensionRing l E (n + 1)` and its `n = 0` residue field. No uniformizer is chosen again. |
| Scheme T, small pro-etale site | `(T : Scheme.{t})`, `Scheme.ProEt.topology T`, object universe `t+1` and morphism universe `t`. |
| R_n constants and B_T inverse limit | The published `integralCoefficientSheaf`, `integralCoefficientSheafSystem`, `completedIntegralCoefficientSheafUnrestricted`, and `limit.π`. The Lean natural index n denotes exponent n+1, so exponent zero never occurs. |
| Unbounded derived category of B_T-module sheaves | `DerivedCategory (scalarReductionSource l E T)`, the actual `SheafOfModules` category for B_T. |
| Quotient-tower completeness with restricted scalars, transitions and canonical maps | The existing `IsDerivedCompleteUnrestricted`. This is the augmented Roos-triangle condition on the canonical derived quotient tower, not an abstract isomorphism with an unrelated limit. The auxiliary finite-field datum in its implementation is existential and ignored by the rings and maps. No characteristic or invertibility condition on T is introduced. |
| Affineness | `hT : IsAffine T`. |
| Evaluation at T sends set-sheaf epis to surjections | `hweak`, quantifying over all morphisms of set sheaves and using `Epi f → Function.Surjective (f.hom.app (op (ProEt.mk (𝟙 T))))`. |
| Finite family | `(J : Type v) [Finite J]`; no inhabitance assumption. |
| Locally constant residue modules with finite-dimensional local models | `F : J → scalarReductionTarget l E T 0` and `hF`, using the recorded `IsLocallyConstantProEtaleModuleSheafWithModelsOfUniverses` with `Module.Finite` over the lifted residue field. Over a field finite generation is finite dimension. |
| Finite clopen partition | `∃ n, ∃ U : Fin n → T.Opens`, with `iSup U = ⊤`, `Pairwise Disjoint`, and `IsClosed (U i : Set T)`. An element of `T.Opens` is its actual open subscheme, with inclusion `(U i).ι`. |
| Simultaneous constant finite free models | For every i and j, `∃ r : ℕ, Nonempty ((F j).over (ProEt.mk (U i).ι) ≅ proEtaleConstantModuleSheafOverOfUniverses ... (ModuleCat.of ... (Fin r → ...)))`. This uses the dependency's slice-site convention; the published weakly-etale localization equivalence identifies that slice with the component's small pro-etale site. |
| Each component quasi-compact | `IsCompact (U i : Set T)`, equivalent to quasi-compactness of the open subscheme. |
| Each component has epi-surjective set evaluation | The displayed universal epi-surjectivity formula at `ProEt.mk (𝟙 (U i).toScheme)`. |
| Evaluation exact for every commutative-ring sheaf C | `∀ C : Sheaf ... CommRingCat.{max w (t+1)}, (SheafOfModules.evaluation ...).PreservesHomology`. Here w is independent of E's universe u; this clause is not restricted to the completed or residue coefficients. In an abelian category this is exactness. |
| Every finite free C-module projective | `∀ r : ℕ, Projective (∏ᶜ fun _ : Fin r ↦ SheafOfModules.unit ...)`. This finite product of the rank-one free sheaf is also its finite direct sum. Mathlib's `Projective` is exactly lifting maps along epis. |
| Canonical completed coefficient comparison | `∃ d : SfClopenCoefficientRestriction ...`; `d.completion` is the inverse orientation of B_T restricted ≅ B_U. `finite_constant` fixes each finite comparison on constant sections, `projection` fixes the completion comparison against every limit projection, and `transition` preserves the finite quotient maps. |
| Ordinary restriction | `sfClopenModuleRestriction` is Mathlib `SheafOfModules.pushforward` along `sfClopenSiteInclusion`, followed by the recorded `SheafOfModules.restrictScalars` along `d.completion.hom`. It retains sections and restriction maps. Exactness fields supply its ordinary induced `mapDerivedCategory`, not an independently selected derived functor. |
| Commutation with derived reductions canonically | `SfClopenCompleteRestriction.reduction` is a natural isomorphism at every positive exponent. `finite_quotient_tensor` fixes the ordinary comparison on sheafified pure tensors; `reduction_counit` identifies the derived comparison with that comparison through the existing scalar-extension counits and canonical localization factors. Thus an arbitrary isomorphism is not substituted for the canonical comparison. |
| Quotients, canonical projections, all transitions | `quotient_tensor` fixes the B-scalar termwise comparison on pure tensors. `tower` is an isomorphism of the actual `ℕᵒᵖ` diagrams, preserving every transition. `tower_quotient` fixes its components to the quotient comparisons, and `tower_unit` explicitly preserves the maps from the original complex. |
| Ordinary restriction preserves completeness | The field `complete` quantifies over every `M` and sends `IsDerivedCompleteUnrestricted ... M` to the same predicate on `sfClopenDerivedRestriction d` applied to M. |
| Same Tor bounds after restriction to every object | The field `tor` quantifies over every M and integers a,b. `SfResidueTorAmplitudeOnEveryObject` uses the recorded exact `ringedDerivedRestrictionGeneral` on every original-site slice. The repaired dependency predicate tests all degree-zero module sheaves L and every q outside the same ordered interval by vanishing of the existing derived-tensor cohomology object. No restriction to free tests, terminal objects, or cohomology of global sections occurs. |
| Empty partition permitted | `Fin n` permits `n = 0`; there is no `Nonempty` hypothesis on T, J, or the partition. Its empty cover equality forces T empty. |

Dependency declarations used (the original records were read, including Mathlib matches):

- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing`, and its coefficient-ring constructions.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `ProEt.topology`.
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `constantSheaf`, `toSheafify`.
- `Mathlib.CategoryTheory.Limits.HasLimits`: `Limits.limit`, `Limits.limit.π`.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`, `Q`,
  `HasDerivedCategory.standard`, `Functor.mapDerivedCategory`.
- `WeilConjectures.CategoryTheory.Triangulated.DerivedLimit`:
  `CategoryTheory.IsDerivedLimit`, `IsDerivedLimitTriangle`, through completeness.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`:
  `SheafOfModules.restrictScalars`.
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`:
  `CategoryTheory.nonempty_derivedChangeOfRingsCochainModel` and its canonical
  change-of-rings interface (publicly imported, not replaced).
- `Sheaf.Paper.ProEtaleLocallyConstantSheafOfUniverses`:
  `Scheme.IsLocallyConstantProEtaleModuleSheafWithModelsOfUniverses`,
  `proEtaleConstantModuleSheafOverOfUniverses`.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `IsOpenImmersion` and the actual opens.
- `Sheaf.AlgebraicGeometry.RingedProEtaleTorAmplitudeOfUniverses`:
  `CategoryTheory.HasRingedSiteTorAmplitudeOfUniverses` (repair below).
- `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`:
  `DerivedCategory.homologyFunctor`. During this work another group landed the
  exact general Mathlib binding for `def-weil-derived-cohomology-sheaves`; that
  landed record is used, and no redundant repair is included here.
- `Sheaf.Paper.DerivedCompleteOnSlices`: its publicly retained
  `WeilConjectures.IsDerivedCompleteUnrestricted` on the global branch.
- `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`: the retained
  `completedIntegralCoefficientSheafUnrestricted`, finite coefficients and projections.
- `Sheaf.Paper.IntegralReductionTowerCanonical`: `canonicalIntegralReductionTower`,
  its canonical legs and cone, and the publicly re-exported `unrestrictedTowerFiniteComplex`,
  `unrestrictedTowerComplex`, `unrestrictedTowerTensorSection`, `unrestrictedTowerUnit`,
  `unrestrictedTowerTransition`. The definition-owner record now explicitly lists these
  five existing declarations; no duplicate tower maps are defined. Their source remains
  `Sheaf.Paper.IntegralReductionTowerWellDefinedUnrestricted`.
- `Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction`:
  `scalarReductionDerivedExtension`, `scalarReductionCounit`,
  `scalarReductionExtension` and its canonical factor comparisons.
- `Sheaf.CategoryTheory.RingedDerivedRestrictionGeneral`:
  `CategoryTheory.ringedDerivedRestrictionGeneral`.
- The Tor predicate uses
  `SheafOfModules.siteDerivedTensorIndependentCoefficients` through its dependency module.
  The tensor-descent theorem is not needed to state the item.
- `Mathlib.CategoryTheory.Sites.Pushforward` and
  `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`:
  `Functor.sheafPushforwardContinuous`, `SheafOfModules.pushforward`.
  These are inlined in the two restriction abbreviations; no gluing theorem is needed
  to define them. The gluing module remains an ordinary proof-plan import.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`:
  `SheafOfModules.over`, `overFunctor` (through the exact derived restriction).

The modules of recorded proof dependencies are imported as the stage-3 proof plan:
weakly-etale localization, constant-module restriction, finite-coproduct evaluation,
weakly-contractible evaluation exactness, clopen module gluing, the pro-etale site,
local surjectivity, Yoneda, scheme coproducts, and open-immersion factorization.
`lem-pur-finite-product-derived-tensor-calculus` has no recorded declaration at
this reading, so there is no module of it to import.

Edge-case reading: J may be empty; T may be empty and take n=0; rank r=0 is allowed
and gives the zero module; finite level n=0 is exponent one (the residue field);
there is no reduction modulo the zeroth power; neither ell-invertibility on T nor a
finite-field base is assumed; disconnected components can have different ranks;
Tor testing retains a≤b and tests every object and module; independent scheme and
coefficient universes are retained. A standard derived localization instance on each
slice is constructed from `HasDerivedCategory.standard`, not assumed as a new
mathematical hypothesis. No goals were checked by a local or global Lake build.

Searches for an existing statement:

- `msearch.py` LeanFinder query "Simultaneous finite clopen trivialization of lisse
  sheaves on weakly contractible affine schemes and restriction preserving derived
  quotient tower completeness": eight affine-limit transition results, none exact.
- `msearch.py` Loogle query `"IsWeaklyContractible"`: zero results.
- `msearch.py` grep query `clopen.*(sheaf|constant)|locallyConstant.*partition` in
  `CategoryTheory/Sites`: zero results.
- `msearch.py` LeanSearch query "Finite clopen partition simultaneously trivializes
  finitely many locally constant finite dimensional module sheaves on a weakly
  contractible affine scheme": eight results (topological clopen-cover partitions,
  locally constant functions, and `Scheme.Modules`), none with this statement.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf`, including the exact node id
  and combinations of clopen, locally constant, quotient tower and completeness:
  no existing exact theorem. The nearby residue-projective-model and finite-clopen
  derived decomposition modules assert different results, with more specialized
  size interfaces; their notions were not copied.
- Read the actual restriction and coefficient APIs in the newly landed clopen-gluing
  module. In this repair, expanded its thin restriction abbreviations to their exact
  Mathlib bodies. Searched scalar-reduction counits before introducing the
  transparent cochain transport: the existing public counit is homotopy-indexed;
  its private cochain transport is not a usable public declaration. The helper
  `sfClopenReductionCounit` is the displayed composition of those existing maps.

No statement correction and no `STATEMENT-DISPUTED` flag are needed.

## Dependency modules

`def-weil-proetale-tor-amplitude` receives a lean-only §1(B) repair in
`Sheaf.AlgebraicGeometry.RingedProEtaleTorAmplitudeOfUniverses`. The recorded
coefficient-sized predicate requires an object in the derived category of an
equivalent small-model site. This node tests the actual ordinary localization of
the residue reduction on all slices of the original site. The older original-site
predicate identifies the scheme and coefficient universes. Neither accepts these
objects. The repair retains the previous module by public import and supplies the
same universal degree-zero-module vanishing test directly on a ringed site with
independent object, morphism, coefficient and localization sizes. Its finite variant
is the existence of one ordered interval. Both definitions are explicit predicates
using the existing derived tensor and `homologyFunctor`, with no postponed data.
Its `lean.declarations` is a superset of NK's landed five-declaration record:
`HasProEtaleTorAmplitude`, `HasFiniteProEtaleTorAmplitude`,
`HasCoefficientModelTorAmplitude`, `HasCoefficientProEtaleTorAmplitude`, and
`HasFiniteCoefficientProEtaleTorAmplitude` all remain recorded and publicly imported,
followed by the two new original-ringed-site predicates.
Every field of this dependency node other than `lean` is unchanged. The final main
module is a concrete compiled consumer of the repaired interface on all residue
slices, including the original pro-etale object/morphism universe pair t+1,t.

`def-weil-integral-reduction-tower` receives a lean-only superset `existing: true`
record in `Sheaf.Paper.IntegralReductionTowerCanonical`. The former record exposed
the canonical tower, its legs and cone and the integral pure-tensor section, but not
the termwise complexes and maps used by this statement. All five former declarations
are retained. Five existing publicly re-exported definitions are added:
`unrestrictedTowerFiniteComplex`, `unrestrictedTowerComplex`,
`unrestrictedTowerTensorSection`, `unrestrictedTowerUnit`, and
`unrestrictedTowerTransition`. These give exactly the node's P_n, restricted scalar
complex, pure tensors, gamma_n and tau_n. This corrects ownership without a new
construction, new node, or change to the dependency's mathematical statement.

## Returned delivery repaired

- H2: the five tower definitions are explicitly recorded under
  `def-weil-integral-reduction-tower`, an existing statement dependency. The
  well-definedness theorem is removed from `stmt_deps` and retained in `proof_deps`.
  The clopen restriction abbreviations now inline the exact Mathlib continuous
  pushforward and module pushforward; the gluing theorem is only a proof dependency.
  The unused site-derived-tensor-descent theorem is removed from `stmt_deps` and
  retained in `proof_deps`. These modules have ordinary proof-plan imports.
- H13: the Tor-amplitude record retains all five declarations of NK's landed record
  and adds the two generalized predicates. Its module publicly imports NK's module,
  which publicly imports the original interface; no published binding is lost.

The retained packet first passed `deliver2.py --no-push` unchanged (82701d352ac).
That mechanical pass did not repair the substantive return. The changes above are
actual edits to both node ownership and the Lean restriction definitions. The
accepted theorem signature and its canonical normalization clauses are retained.

## Second reading by Q28

The dispatch explicitly prohibits starting other agents and assigns independent
review to the maintainer. No independent worker reading is claimed here. An author
rereading compared every hypothesis and clause with the node, including the repaired
dependency: it retained empty partitions and zero ranks, used the published ordinary
restriction, removed an unnecessary K-flatness conclusion, separated the arbitrary
ring-sheaf universe from E, and fixed the derived comparison by its pure-tensor and
counit normalization. The maintainer's independent review remains the independent
second reading required by this dispatch.

Validation: both delivered files compile separately in dependency order through
`scompile.py`, including their real module names against the published live library.
The only postponed proof is the item's named theorem. Delivery preflight and its
per-file compilation are run with `deliver2.py --no-push` before delivery.

## Maintenance baseline and final validation (2026-10-21)

The initial saved-packet dry run passed: commit 7abe6ad6b27 compiled all three
server inputs and passed preflight. The earlier proof-dependency gate rejection
is resolved by the maintainer's 2026-10-21 baseline repair. The sandbox item's
metadata is now rebased on the current shared record, including both required
theorems in proof_deps and in proof step 6's uses. No mathematical statement,
source, or proof-step text changed; only the repaired Lean binding and the added
landed definition dependencies differ from the current baseline. No statement
correction is claimed or needed.

The final author self-check reread both delivery modules against H2/H13: tower
helpers are recorded under their definition node; restrictions directly use
Mathlib pushforward; well-definedness, tensor descent, and gluing remain proof
dependencies only. Both dependency records are supersets retaining all five
previously published declarations and change only lean. The main theorem's
canonical comparison and normalization clauses are unchanged. Both recorded
signatures match the source verbatim, all variables and universes are explicit,
all lines are at most 100 characters, the dependency module has no sorry, and
the item's named theorem has the only sorry. The final packet is checked again
with the prescribed dry run before delivery.
