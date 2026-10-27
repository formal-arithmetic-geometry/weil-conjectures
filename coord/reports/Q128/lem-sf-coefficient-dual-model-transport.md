## Worker report

Q128 states `lem-sf-coefficient-dual-model-transport` in
`lean/Sheaf/Paper/CoefficientDualModelTransport.lean`, namespace
`WeilConjectures.CoefficientDualModels`. The clauses are separate named statements
in one module, all recorded in `lean.declarations`. Every theorem has proof `sorry`
and a source/proof docstring. Definitions construct actual objects or select an
object determined by an explicit uniqueness or derived universal property.

The previous worker's no-change response did not complete stage 2: Q101's record
is the stage-1 split review, and the node had no `lean` record. This delivery
supplies the missing statement. The mathematical node statement, proof and
proof dependencies are unchanged. Its statement-dependency list cites definition ownership records for the public
slice, normalized scalar-unit and pure-section interfaces. Three new existing:true
ownership nodes record already-published constructions; no Lean construction is duplicated.

### Hypotheses and clause correspondence

* The prime is `(l : ℕ) [Fact l.Prime]`. The finite coefficient extension is
  `(E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]`.
  The valuation ring and uniformizer are exactly
  `Padic.coefficientExtensionIntegers l E` and
  `Padic.coefficientExtensionUniformizer l E`. A coefficient inclusion is an
  actual `ℚ_[l]` algebra homomorphism `ι : E →ₐ[ℚ_[l]] L` between finite extensions;
  it is injective because it is a field homomorphism. The common-stage section
  quantifies actual finite subfields of the fixed algebraic closure `Ω`.
* The scheme is arbitrary `X : Scheme.{t}` on the ambient/slice side. Its site
  has object universe `t+1` and morphism universe `t`; coefficient modules live
  in `max u (t+1)`. There is no imposed equality between site and coefficient
  universes. The recorded constructible/common-stage conventions use
  `X : Scheme.{u}` and `Coefficient.{u} l Ω E`, independently of the universe `v`
  containing `Ω`. Invertibility is the explicit
  `∀ x : X, IsUnit (l : X.presheaf.stalk x)` in the restriction theorem and in
  construction of the constructible unit. The ambient algebra statements do
  not need this hypothesis on arbitrary module complexes.
* The sites, rings, modules and derived categories are the existing
  `IntegralOnSlice.Site`, `topology`, `ring`, `Mod`, `Cx`, and `D`. `none` is the
  global site; `some U` is the actual over-site. `unit` is `q.obj coefficient`.
  `dual_existsUnique` specifies `dual` on unchanged objects by the ambient
  K-injective `IntegralOnSlice.hom` into that coefficient, and specifies its
  contravariant action on every pure fraction arrow. It is not a Karoubi dual,
  an external Hom group, or a discrete-field sheaf construction.
* The constructible-domain qualifier is exactly
  `constructibleRationalHomPairs l E X (op K, stageUnit ...)` in `stageDualPair`
  and `stageDual`. Their internal Hom is the dependency's
  `rationalDerivedInternalHom`, with no extra projectivity or dualizability
  assumption. `stageDualMap` is that functor's actual map of the permitted pair.
  `stageInclusion` retains the actual underlying integral objects and pure
  fraction arrows; `stageDual_ambient` identifies the specified constructible
  dual with the ambient dual. This permits arbitrary ambient resolutions and
  slice inputs without claiming that all of them are constructible.
* `coefficientDualModelTransport` gives natural isomorphisms
  `dual_U ⋙ restrictionRational ≅ restrictionRational.op ⋙ dual_V`.
  Their components are explicitly the rationalization of
  `integralDualRestriction`, itself the dependency's ambient `homIso` followed
  by Hom of the actual `restrictionCoefficientIso`. The integral data are
  `Normalized` and `CompletedRestrictionComparisons.Coherent`, so the component
  prescription carries the successive-restriction identities to the raw
  rational maps. The family `η` states `H(E_U) ≅ E_U`; the final equality is
  precisely its restriction/unit square. Both global restriction and
  relocalization are included by `RestrictionArrow`.
* `free U m` is the actual finite sum of completed units in degree zero,
  rationalized. `dualFiniteFreeRetract` quantifies a genuine degree-zero module
  `F`, localized maps `i`, `p`, and the retraction equality `i ≫ p = 𝟙 _`.
  The output maps are `H.map p.op ≫ e.hom` and `e.inv ≫ H.map i.op`, with their
  composite equal to the identity. No integral representatives of these maps
  satisfying a retraction equation are assumed.
* `scalarRing` restricts the existing `completedCoefficientMap`. `scalarModules`
  and `scalarDerived`, together with `scalarCounit`, use the recorded actual
  change-of-rings universal data for this ring map. `scalarExact` asserts its
  exactness and termwise computation on **every** complex. Thus these are
  ordinary finite-free scalar tensor functors, and the completed-scalar
  comparison on complete inputs identifies them with the specified functor
  on the constructible domain. `scalarRational_existsUnique` prescribes the
  precise field map on coefficients and integral scalar map on pure arrows.
  `scalarDualComparison` is a natural isomorphism for ambient slice duals;
  `stageScalarDual` uses precisely the recorded constructible scalar functor.
* `RationalModules`, `qModules`, and `freeModule` are the same raw scalar
  localization applied to the actual module sheaves. `moduleLinear` specifies
  the constant-section action used in it. `Models U P K a b` means an actual
  complex with support in `[a,b]` has a localized chain isomorphism to `P` and
  its derived image is `K`. This is a presentation relation, not a choice of
  an arbitrary realization. It admits rational differentials: the bounded
  lifting clause of the existing proof dependency
  `lem-sf-localized-signed-dual-presentation` supplies such a presentation.
  Retraction maps are never lifted. `RetractTerms` retains the actual
  localized arrows `i,p` term by term.
* `scalarRationalComplex` applies scalar tensor to both objects and localized
  differentials. `scalarLocalModels` assumes exactly a bounded supplied local
  dual model and its term retractions, and returns the **same** bounds, a model
  for the dual of the scalar-extended input, term retractions, and the displayed
  images of every supplied retraction through the finite-free comparison.
  The theorem is for an arbitrary slice `U` and arbitrary integers `a,b`.
  Applying it separately to each member of any supplied coefficient-site cover
  requires no uniform bounds or ranks over that cover.
* `scalarTailTriangles` records the exact triangle isomorphism for termwise
  scalar tensor on a complex short exact sequence, with all three components
  equal to the canonical computing counits. Its last equation explicitly
  includes `DerivedCategory.triangleOfSESδ` and the shift comparison, after
  scalar localization. The stupid-tail sequences are the degreewise split
  special cases; inclusion and projection are the first two triangle arrows.
  A bounded rational model is transported through its localized chain
  presentation, so this covers its actual tail comparison maps as well.
* Scalar/restriction compatibility is a square of actual maps, not two
  unconnected existence statements. `scalarModuleRestriction` is uniquely
  fixed by the formula sending a restricted sheafified tensor generator to
  the same tensor generator. `scalarDerivedRestriction` is uniquely fixed by
  its computing square on every complex, and `scalarRationalRestriction` by
  its localized components. `scalarRestrictionDualCompatibility` gives both
  the dual square and the coefficient-unit square with these maps, and
  retains the integral normalization of both Hom restriction comparisons.
* `finiteScalarDualCoherence` quantifies **one** family `ε,β` over all finite
  subfields and inclusions, and spells out the normalization and equations.
  `β` is the recorded `rationalHomScalarComparison` followed by Hom of `ε`.
  `ε` is normalized after ambient inclusion to the already-published
  `constantCoefficientIntegralScalarIso`, whose inverse strict unit has its
  quotient coordinates and zero shifted coordinate specified. It is therefore
  not an arbitrary unit isomorphism. The remaining clauses are the identity
  unitor, the unit tower equation, the dual tower equation (including the
  inverse first-variable associator), and contravariant naturality in `K`.
  The associator and unitor are the dependency's specified tensor comparisons.
* `commonDual_permitted` and `commonDualPair` put the original permitted pair
  in the **recorded** common-stage Hom domain. `commonDual` is literally
  `commonStageHomObject` on that pair; this is the object formula of
  `commonStageDerivedInternalHom`. `commonStageDualModelTransport` identifies
  it with the inclusion of `(E,H_E(K))` and with the dual at **every** further
  finite coefficient stage. Together with the preceding family tower equation
  and the common-stage category's eventual-equality convention, this states
  independence of any further common finite extension. The local models and
  their extensions represent these objects by `scalarLocalModels`.
* No declaration assumes separatedness, quasi-compactness, a uniform degree
  interval over a cover, a lattice splitting, or lifting of localized
  retractions. There is no statement correction or disputed statement.

### Dependencies used

The original statement dependencies were read with their recorded declarations
and signatures. The size convention is a convention rather than an additional
Lean object. The pro-etale site uses Mathlib's `Scheme.ProEt` and its topology;
the localized ringed site uses Mathlib's actual `overFunctor` and `overMap`;
cochain complexes use `CochainComplex`/`HomologicalComplex`.

The remaining original declarations used are:

* `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`: its reexported actual
  completed coefficient ring and quotient system.
* `Sheaf.Paper.DerivedPullbackTensorHom`:
  `constructibleRationalHomPairs`, `rationalDerivedInternalHom`,
  `rationalHomScalarPair`, `rationalHomScalarComparison`, `commonStageHomPairs`,
  and `commonStageHomObject` (the recorded common-stage Hom object formula).
* `Sheaf.Paper.SfRationalizationKaroubi`:
  `sfRationalConstructibleCategory`, `sfRationalConstructibleLocalization`,
  `sfRationalCoefficientEquiv`, and `sfRationalScalarExtension`.
* `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients`: the actual pair category,
  `Coefficient`, `inclusion`, `transition`, `stageTransition`, `associator`, `unitor`.
* `Sheaf.CategoryTheory.ScalarLocalization`: `ScalarLocalization` and its actual
  localization functor and fraction Hom modules.
* `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses`:
  `derivedInternalHomOfUniverses`, through the recorded slice `hom`.

The added definition statement dependencies provide the public slice and
normalization interfaces:

* `def-pur-integral-derived-operations`, module
  `Sheaf.Paper.IntegralDerivedOperationsOnSlices`: `IntegralOnSlice.Site`,
  `topology`, `restrict`, `ring`, `rings`, `Mod`, `Cx`, `D`, `hom`, `duality`.
* `def-sf-raw-rational-slice-coefficients`, module
  `Sheaf.Paper.RationalThickEvaluation`: `coefficient`, `scalarConstant`,
  `Rational`, `q`, and their canonical linear structures.
* `def-sf-completed-slice-restriction-data`, module
  `Sheaf.Paper.RationalSliceCompletedEvaluation`: `RestrictionArrow`, actual
  restriction functors, `restrictionLocalization`, `restrictionSection`,
  `restrictionCoefficientIso`, `CompletedRestrictionComparisons`, its
  `Normalized` and `Coherent` predicates.
* `def-weil-completed-integral-scalar-data`, module
  `Sheaf.Paper.CompletedIntegralScalarData`: the transparent
  `completedIntegralScalarCoefficientMap` alias of `completedCoefficientMap`. The generic
  `derivedChangeOfRingsIndependentCoefficients` supplies the exact ordinary
  object/map and universal derived-counit data.
* `def-fix-ringed-scalar-extension-section`, module
  `Sheaf.SixFunctors.RingedFiniteFreeHomBaseChangeData`:
  `ringedFiniteFreeScalarSection`. The Hom theorem module is a proof import.
* `def-sf-normalized-constant-coefficient-scalar-unit`, module
  `Sheaf.Paper.ConstantCoefficientScalarNormalization`:
  `constantCoefficientIntegralScalarIso`, with its strict-cone normalization.
  Its finite-field-independent signature, not a choice of a finite-field datum,
  is used for the actual coefficient unit.

All recorded proof-dependency modules are imported, publicly when their data
occur in signatures and otherwise privately. The three proof dependencies with
no recorded module are `lem-weil-pbc-exact-functor-derived-factorization`,
`lem-sf-localized-signed-dual-presentation`, and
`lem-weil-pbc-degreewise-split-connecting-morphism`; they are proof inputs only,
not missing objects in the statement. Their roles are recorded in the theorem
proof docstrings. The actual SES boundary declaration and scalar triangulation
modules are imported. No import is replaced by a private copy of its definitions.

### Edge cases and searches

Checked on the statement: rank zero (the empty free sum and zero dual), zero
complexes, the empty scheme, single-term models, empty support intervals
`b < a`, identity restriction, repeated restriction, identity coefficient
extension, ramified finite extensions, and three coefficient stages. The slice
and coefficient universes remain independent. All rational retraction arrows
are permitted fractions, including sums of pure tensors.

Searches actually run with the prescribed `msearch.py` wrapper (see the sandbox
`searches.jsonl`):

* `leanfinder`, query `Restriction and finite field scalar extension of derived
  internal Hom dual models of constructible rational proetale sheaves`:
  eight hits, including `LightCondensed.ihom_map_val_app`,
  `LightCondensed.ihomPoints_symm_comp`, and condensed/solid-module results.
  None gives the actual completed-coefficient/raw-rational/common-stage statement.
* `loogle`, query `CategoryTheory.Sheaf, CategoryTheory.Linear`: zero hits.
* `grep`, query `scalar.*extension|extension.*scalar|internalHom|RHom` under
  `CategoryTheory/Sites`: eighteen hits, chiefly Point/Monoidal and IsSheafFor;
  no coefficient-dual-model transport theorem.
* Repository `rg` searches for this node id and dual-model/transport names in
  both `lean/WeilConjectures` and `lean/Sheaf` found no existing theorem for this
  item. Searches and source reads did find the recorded slice, finite-free
  scalar, common-stage and normalized-unit APIs reused above. The generic
  structures alone do not state this assembled coefficient-model theorem.

## Repair of the returned delivery

H2: the five theorem statement dependencies added by the first packet are removed.
The original ten dependencies are preserved verbatim. The item now cites only
definition nodes. `def-sf-raw-rational-slice-coefficients` owns `Rational`, `q`,
`coefficient` and their constant scalar action in RationalThickEvaluation.
`def-sf-completed-slice-restriction-data` owns the actual restriction functors,
coefficient comparison and normalized/coherent comparison predicates.
The already-landed `def-weil-completed-integral-scalar-data` owns the transparent
`completedIntegralScalarCoefficientMap` alias of `completedCoefficientMap`, and `def-fix-ringed-scalar-extension-section` owns
`ringedFiniteFreeScalarSection`. The new normalized scalar-unit node owns
`constantCoefficientIntegralScalarIso`. The generic tensor model is cited via
`def-coef-ringed-tensor-hom-model`. No theorem is relabeled as a definition.

H3: the existing partial repair was retained and completed. `integralUnitEvaluation`
is the closed evaluation at one, using the normalized ordinary tensor unitor;
`coefficientDualModelTransport` fixes every eta.hom to its rational image.
`dualFiniteFreeRetract` fixes each coordinate to evaluation on the actual standard
generator, so the isomorphism cannot be changed by an arbitrary automorphism.
`IntegralScalarUnitNormalized` fixes multiplication on sheafified pure sections
and the derived computing counit. `ScalarTensorNormalized` fixes the strong tensor
map on generators and on all K-flat computation squares. `ScalarDualNormalized`
fixes its Hom map to the finite-free extended-evaluation transpose, followed by
Hom of that multiplication unit. Both beta and epsilon at U and V in
`scalarRestrictionDualCompatibility` satisfy these normalizations independently.
Thus the unit square compares specified maps. `scalarLocalModels` fixes every
finite-free module comparison on each standard generator and all scalar sections.

The remaining three bare-isomorphism statements have been repaired.
`stageDual_ambient` specifies the identity on the common integral Hom representative.
`stageScalarDual` specifies epsilon by the published integral scalar-unit iso and
beta by `rationalHomScalarComparison` followed by Hom(epsilon).
`commonStageDualModelTransport` specifies its first comparison by the published
`commonStageHomComparison`, the common-stage `isoToStage`, and the scalar unitors
on both Hom inputs, preceded by the published identification of the recorded
stage transition with scalar extension. At any further field, beta uses the same normalized scalar-Hom
formula, and the comparison back to the original common dual is its inverse,
followed by `operationStageTransitionIso` in the inverse direction, the published
stage-transition isomorphism and the first comparison's inverse. These are explicit maps, not independent Nonempty isomorphisms.

## New nodes

`def-sf-raw-rational-slice-coefficients` records the existing raw slice category,
coefficient and constant scalar action of RationalThickEvaluation. Its source is
the local-dual paragraph's rational coefficient convention, implemented using
`def-pur-integral-derived-operations` and `def-weil-linear-scalar-localization`.
LeanSearch, LeanFinder and Mathlib grep searches returned only general module
localization or scalar-action results. DAG and project searches found the exact
published definitions but no definition ownership node, so this is existing:true.

`def-sf-completed-slice-restriction-data` records the existing actual restriction
and normalized comparison data of RationalSliceCompletedEvaluation, including
Normalized and Coherent. It asserts no existence theorem. Source: the local-dual
paragraph and Stacks 03DJ/08JB/08TC. The same three search types, DAG searches and
blueprint search found no owner node, and the exact source definitions are reused.

`def-sf-normalized-constant-coefficient-scalar-unit` records the existing strict
regular-unit and integral scalar-unit isomorphism of ConstantCoefficientScalarNormalization.
Source: the local-dual paragraph and Bhatt--Scholze 6.8.2. Its inverse has the
prescribed quotient coordinates and zero shifted coordinate. The searches found
the exact project construction and no definition ownership node; no new module
or arbitrary isomorphism is introduced.

## Second reading by Q128

This is the worker's own self-check; the dispatcher prohibits other agents and
the maintainer provides the independent review. The return's H2 and H3 findings
were checked against the node and the actual dependency sources. The prime,
finite extensions, arbitrary scheme, stalk invertibility, raw localization and
constructible-domain restrictions are unchanged. The module still has arbitrary
slice bounds, actual rational retractions with no integral lift, and the full
connecting-map equation for tail triangles. The new clauses specify the maps
whose naturality the source asserts; they do not add hypotheses to that source.
All ownership nodes point to existing plain definitions. Rank zero has no generator
conditions and its zero-object maps are unique; empty intervals force zero models.
Identity coefficient extensions and restrictions use the same multiplication and
unitors; repeated stages retain the specified inverse first-input comparison.

Validation: the prescribed `scompile.py Q128 lem-sf-coefficient-dual-model-transport
lean/Sheaf/Paper/CoefficientDualModelTransport.lean` passed both sandbox and library
compiles (44.4 s and 43.2 s), with no errors or warnings. Derived change-of-rings
universes and its counit type are explicit; sequential elaboration avoids repeated
expansion of the large universal witness. The required delivery dry run follows.
