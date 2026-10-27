## Worker report

Q66 states `lem-sf-closed-direct-image-strict-reduction` in
`Sheaf.AlgebraicGeometry.ClosedDirectImageStrictReduction`. The theorem has `sorry`;
no theorem is proved in this delivery. The other module defines the universal cochain presentation in the new
`def-sf-integral-strict-reduction-model` node under §1(A). The original
`def-weil-integral-reduction-tower` record is restored exactly, with no delta.
The mathematical statement and the main theorem signature are unchanged.

Hypotheses and clauses, checked individually:

- Prime ell is `(l : ℕ) [Fact l.Prime]`. The coefficient extension is `(E : Type u)
  [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]`. The published
  coefficientExtensionRing, finite quotient sheaves, completed sheaf and scalar
  extension functors supply O_E and its uniformizer-power quotients. Lean n means
  exponent n+1, so all and only positive powers occur. No extra characteristic
  or invertibility hypothesis is imposed by the main theorem.
- Schemes are `X Z : Scheme.{t}`, independently of coefficient universe u.
  `i : Z ⟶ X` has `[IsClosedImmersion i]`. The qc open complement is `U : X.ProEt`,
  `[IsOpenImmersion U.hom] [QuasiCompact U.hom]`, and
  `hU : Set.range U.hom = (Set.range i)ᶜ`. A pro-etale object introduces no further
  restriction: an open immersion is weakly etale. Neither X nor Z is assumed qcqs.
- Small pro-etale sites, finite constant sheaves, inverse-limit coefficients and
  their canonical ring maps are the existing `integralCoefficientCommRingSheaf`,
  `completedIntegralCommRingSheafUnrestricted`, `IntegralAmbient.push`, and
  `Scheme.coefficientProEtaleDirectRingMap`. The latter is used explicitly in the
  pure-tensor formula; no arbitrary coefficient-ring identification is assumed.
- `scalarReductionSource` is the published category of completed-module sheaves;
  `DerivedCategory` is the ordinary unbounded derived category. Strict varying
  systems are `coefficientSequenceModules` on the existing ringed sequence site;
  `coefficientSequenceDerived` is its actual derived category. This is not a
  diagram valued in individual derived categories.
- The exact ordinary system image is `integralComparisonSequenceDirectImage i`.
  `ExactImages` records finite-limit/colimit preservation of it and completed
  direct image. Importantly, the theorem concludes `∃ (_h : ExactImages l E i), ...`;
  there is NO additional exactness premise. `omit [ExactImages l E i] in` ensures
  the surrounding notation's certificate is not a theorem hypothesis.
- `SX SZ : IntegralStrictReductionModel ...` are arbitrary presentations of the
  specified simultaneous derived reduction. This record pins the ordinary
  functor to the existing finite scalar extensions by `level`; `transition` pins
  every semilinear quotient map. Its `augmentation_sections` is x ↦ 1 tensor x.
  `universal` specifies the left-derived functor, and `computes` uses ONE flat-term
  K-flat complex to compute the entire system. `evaluation_normalized` identifies
  each finite evaluation with the published finite K-flat computation. Thus these
  binders specify the reductions named by the node rather than replacing them
  by arbitrary functors. This interface defines normalized presentation data without choosing a witness.
- `Comparison.r` is a natural ISOMORPHISM
  `(IntegralAmbient.push i).mapDerivedCategory ⋙ SX.reduction ≅
  SZ.reduction ⋙ integralComparisonSequenceDirectImage.mapDerivedCategory`.
  In particular its component is precisely R_X(i_*P) ≅ I R_Z(P).
- `Comparison.projection : IsProjectionNormalized ... r` pins this system map on
  resolving presentations. Given flat-term K-flat P on Z, Q on X and a quasi-iso
  f:Q→i_*P, it asks for one actual strict-system cochain map c. At EVERY degree,
  level, site object and pure tensor, c sends b tensor x to i^-1(b) tensor f(x),
  using the existing sheafified `unrestrictedIntegralTensorSection`. The canonical
  sectionwise coefficient map appears explicitly. Tensor notation in the library
  writes the scalar first; this is s tensor a ↦ s tensor i^-1(a) in the node's
  notation. The following equation includes both exact localization factors and
  both universal counits, so it identifies the actual r, not only its evaluations.
  Coupled with `evaluation_normalized`, this is the node's canonical finite
  derived closed projection comparison, not an unspecified finite isomorphism.
- All quotient transition equations hold because c and r are morphisms in the
  strict-system cochain and derived categories, respectively. No evaluated family
  of maps is lifted to a system morphism.
- `Comparison.restriction` identifies scalar restriction of I with termwise
  completed direct image. `restriction_sections` pins it to identity on sections.
  `derivedRestriction` is its canonical exact localization with both composition
  factors; `constantSquareDerived` similarly localizes the existing constant square.
- `Comparison.aX` and `aZ` are natural transformations from the DERIVED constant
  strict completed-module towers, into scalar restriction of the reductions.
  `IsAugmentationNormalized` pins them on good complexes to the actual ordinary
  quotient augmentation via the universal counit and exact localization factors.
  `Comparison.augmentation` is the full equation between transformations into
  D(strict completed-module towers), including the scalar-restriction comparison
  and constant-direct-image square. No evaluation has been used in place of this
  system-level equation.
- No constructibility, derived completeness, cohomology bound, Tor-amplitude or
  flatness of quotient rings is required. The only flat/K-flat conditions occur
  in the universally quantified representative NORMALIZATION test, as the node
  explicitly specifies for computing a derived functor.

The theorem docstring reproduces all eight proof steps and their cited node ids.
The model module defines only presentation data and equations; it asserts no existence theorem.
Definitions contain actual terms or specify structures; no sandbox definition chooses an
object from a bare `Nonempty` theorem with postponed proof.

Dependency declarations read (module prefixes are literal import paths; the three
theorem-only owners listed here have been replaced as statement dependencies by
the definition owners detailed in Returned delivery repairs):

- `def-weil-l-adic-coefficient-extension`: `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`, `Padic.finite_coefficientExtensionRing`.
- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme`.
- `def-weil-closed-immersion`: `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`, `AlgebraicGeometry.IsClosedImmersion`.
- `def-weil-open-immersion`: `Mathlib.AlgebraicGeometry.OpenImmersion`, `AlgebraicGeometry.IsOpenImmersion`.
- `def-weil-finite-type-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`, `AlgebraicGeometry.LocallyOfFiniteType`.
- `def-weil-pbc-proetale-site`: `Mathlib.AlgebraicGeometry.Sites.Proetale`, `AlgebraicGeometry.Scheme.ProEt`.
- `def-weil-pbc-constant-sheaf`: `Mathlib.CategoryTheory.Sites.ConstantSheaf`, `CategoryTheory.constantSheaf`.
- `def-weil-completed-integral-coefficients`: `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`, `WeilConjectures.integralConstantToCompletionOfUniverses`.
- `lem-weil-pbc-profinite-coefficient-inverse-image`: `Sheaf.AlgebraicGeometry.ProfiniteCoefficientInverseImage`, `AlgebraicGeometry.Scheme.proEtale_profinite_coefficient_inverse_image`.
- `def-weil-sheaf-of-modules-category`: `Sheaf.CategoryTheory.RingedSiteModules`, `CategoryTheory.ringedSiteModules`.
- `def-weil-abstract-derived-category`: `Mathlib.Algebra.Homology.DerivedCategory.Basic`, `DerivedCategory`.
- `lem-pur-coefficient-system-derived-comparison`: `Sheaf.Paper.CoefficientSystemDerivedComparison`, `SheafOfModules.coefficientSystemDerivedComparison`.
- `lem-weil-pbc-proetale-ringed-open-closed`: `Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed`, `AlgebraicGeometry.Scheme.proEtale_ringed_open_closed`.
- `def-weil-exceptional-inverse-image`: `Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients`, `WeilConjectures.ConstructibleExceptionalCoefficients.System`.
- `def-weil-integral-reduction-tower`: `Sheaf.Paper.IntegralReductionTowerCanonical`, `WeilConjectures.canonicalIntegralReductionTower`.
- `def-pur-sheaf-tensor-product`: `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`, `SheafOfModules.cochainModulesMonoidal`.
- `def-weil-exact-derived-adjunction`: `Sheaf.CategoryTheory.ExactDerivedAdjunction`, `SheafOfModules.OpenTensorNormalization.exactDerivedAdjunction`.
- `def-weil-proetale-inverse-image`: `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`, `AlgebraicGeometry.Scheme.proEtaleSheafInverseImage`.
- `lem-exc-open-closed-detection`: `Sheaf.AlgebraicGeometry.ProEtaleOpenClosedDetection`, `AlgebraicGeometry.Scheme.proEtaleRingModule_isZero_of_open_closed`.
- `lem-pur-derived-change-of-rings`: `Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings`, `ModuleCat.nonempty_ordinaryDerivedChangeOfRings`.
- `lem-pur-proetale-inverse-image-tensor-comparison`: `Sheaf.AlgebraicGeometry.ProEtaleInverseImageTensorComparison`, `AlgebraicGeometry.ProEtaleTensorComparison.inverseImage_tensor_comparison`.
- `lem-sf-exact-functor-derived-triangulated`: Mathlib match `{'declaration': 'CategoryTheory.Functor.mapDerivedCategory', 'file': 'Mathlib/Algebra/Homology/DerivedCategory/ExactFunctor.lean', 'how': 'exact: `F.mapDerivedCategory` with the instances `CommShift ℤ` and `IsTriangulated`, and `F.mapDerivedCategorySingleFunctor n` for complexes concentrated in degree $n$'}`.
- `lem-sf-ringed-closed-kernel-adjoint`: `Sheaf.AlgebraicGeometry.ProEtaleRingedClosedKernelAdjoint`, `AlgebraicGeometry.Scheme.proEtale_ringed_closed_kernel_adjoint`.
- `lem-weil-pbc-localization-universal-property`: Mathlib match `{'declaration': 'CategoryTheory.Localization.lift', 'file': 'Mathlib/CategoryTheory/Localization/Predicate.lean', 'how': "specializes in one line, one declaration per clause, for `L : C ⥤ D` with `[L.IsLocalization W]` (Mathlib's notion of localization; `DerivedCategory.Q` is one for `HomologicalComplex.quasiIso C (ComplexShape.up ℤ)`, DerivedCategory/Basic.lean:98): (1) `Localization.lift F hF L` (line 304) with `Localization.fac F hF L : L ⋙ lift F hF L ≅ F` (line 313); (2) `Localization.liftNatTrans L W F₁ F₂ F₁' F₂' τ` (line 326, for `[Lifting L W Fᵢ Fᵢ']`, the class holding the isomorphisms φᵢ, line 295) with `liftNatTrans_app` (line 332), `liftNatTrans_id` and `comp_liftNatTrans` (lines 339-351), `liftNatIso` (line 357); uniqueness in (2) and clause (3) is `Localization.natTrans_ext` (line 286); the equivalence of functor categories is `Localization.fullyFaithfulWhiskeringLeft` (line 278) with `Localization.essSurj`"}`.
- `lem-weil-pbc-proetale-closed-underived-projection`: `Sheaf.AlgebraicGeometry.ProEtaleClosedUnderivedProjection`, `AlgebraicGeometry.ProEtaleClosedProjection.closed_underived_projection`.
- `lem-weil-pbc-proetale-immersion-limit-preservation`: `Sheaf.AlgebraicGeometry.ProEtaleImmersionLimitPreservation`, `AlgebraicGeometry.Scheme.proEtale_immersion_inverseImage_preservesLimits`.
- `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`: `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`, `SheafOfModules.CanonicalTensorPullbackOfUniverses.ringedTopoiCanonicalDerivedTensorPullback`.
- `lem-weil-pbc-site-derived-tensor-descent`: `Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`, `SheafOfModules.site_derived_tensor_descent_independentCoefficients`.
- `def-coef-ringed-sequence-site`: `Sheaf.Paper.CoefficientRingedSequenceSite`, `WeilConjectures.coefficientSequenceCommRingSheaf`.
- `lem-coef-derived-system-evaluation-calculus`: `Sheaf.Paper.CoefDerivedSystemEvaluationCalculus`, `WeilConjectures.coefficientDerivedSystemEvaluationCalculus`.
- `def-trf-integral-comparison-sequence-systems`: `Sheaf.Paper.IntegralComparisonSequenceSystems`, `WeilConjectures.integralComparisonDerivedSequencePullback`.
- `lem-pur-integral-ambient-operation-models`: `Sheaf.Paper.IntegralAmbientOperationModels`, `WeilConjectures.IntegralAmbient.integralAmbientOperationModels`.
- `lem-weil-pbc-reduction-pullback-derived-tower`: `Sheaf.Paper.ReductionPullbackDerivedTower`, `CategoryTheory.StrictReduction.reductionPullbackDerivedTower`.

The model module publicly imports the original reduction-tower module. Its original
node record and all of its exports are retained unchanged. Definition dependencies
now own the sequence site, actual sequence direct image, flat-term K-flat predicate,
ordinary termwise functor and exactness instances, ordinary constant square,
completed module direct image and finite computation maps.
The generic tensor, exact-adjunction, localization, pullback tensor, closed projection
and open/closed detection modules remain ordinary proof imports, including those
only used by the future proof.

Edge cases checked before/following formulation: identity i with empty U; empty Z
and U=X; both schemes empty; zero and genuinely unbounded complexes; n=0 (exponent
one), m=n and arbitrary n≤m; non-flat quotients; independent scheme/coefficient
universes. Section identities specialize to their identity/zero versions; no
invertibility of ell, common cohomological bound, or excluded identity case occurs.
The generalized interface avoids forcing the site's object universe t+1 and
morphism universe t to equal the coefficient universe.

Searches for an existing declaration:

- grep: `closed.*(reduction|strict)|strict.*(reduction|projection)`: 25 hits; Mathlib/Geometry/Euclidean/Projection.lean, Mathlib/Geometry/Euclidean/Projection.lean, Mathlib/Geometry/Manifold/LocalInvariantProperties.lean, Mathlib/Geometry/Manifold/LocalInvariantProperties.lean, Mathlib/Geometry/Manifold/LocalInvariantProperties.lean, Mathlib/Geometry/Manifold/LocalInvariantProperties.lean, Mathlib/Geometry/Manifold/LocalInvariantProperties.lean, Mathlib/Topology/Algebra/Valued/ValuationTopology.lean. 
- loogle: `CategoryTheory.Functor.mapDerivedCategory, CategoryTheory.NatIso`: 0 hits; . loogle: unknown identifier 'CategoryTheory.NatIso'
- leanfinder: `Closed immersion direct image commutes with simultaneous derived reduction of strict coefficient systems preserving quotient augmentation`: 8 hits; AlgebraicGeometry.IsClosedImmersion.spec_of_quotient_mk, AlgebraicGeometry.Scheme.Hom.liftQuotient_comp_assoc, IsAdicComplete.StrictMono.mkQ_comp_lift, AdicCompletion.transitionMap_comp_reduceModIdeal, AlgebraicGeometry.Scheme.Hom.liftQuotient_comp, IsAdicComplete.StrictMono.factorPow_comp_eq_of_factorPow_comp_succ_eq', AlgebraicGeometry.Scheme.Hom.liftQuotient, AlgebraicGeometry.Scheme.IdealSheafData.glueDataObjHom_comp. 
- loogle: `CategoryTheory.Functor.mapDerivedCategory`: 12 hits; CategoryTheory.Functor.mapDerivedCategory, CategoryTheory.Functor.instCommShiftDerivedCategoryMapDerivedCategoryInt, CategoryTheory.Functor.mapDerivedCategoryIdIso, CategoryTheory.Functor.mapDerivedCategorySingleFunctor, CategoryTheory.Functor.instIsTriangulatedDerivedCategoryMapDerivedCategory, CategoryTheory.Functor.instLinearDerivedCategoryMapDerivedCategory, CategoryTheory.NatTrans.instCommShiftDerivedCategoryMapDerivedCategoryInt, CategoryTheory.Functor.instLiftingCochainComplexIntDerivedCategoryQQuasiIsoUpMapDerivedCategoryId. 
- leansearch: `Closed direct image commutes with simultaneous derived reduction of strict coefficient systems with quotient augmentation`: 8 hits; AdicCompletion.transitionMap_comp_reduceModIdeal, CategoryTheory.ObjectProperty.isoClosure_strictMap, AlgebraicGeometry.IsClosedImmersion.isStableUnderBaseChange, CategoryTheory.Functor.instCommShiftCochainComplexIntDerivedCategoryHomMapDerivedCategoryFactors, AlgebraicGeometry.Scheme.Modules.restrictFunctorAdjCounitIso, AlgebraicGeometry.universallyClosed_isStableUnderBaseChange, AlgebraicGeometry.descendsAlong_universallyClosed_surjective_inf_flat_inf_quasicompact, CategoryTheory.Functor.mapDerivedCategoryFactorsh. 
The initial two-name Loogle query used the invalid name CategoryTheory.NatIso;
the successful single-name query was rerun and inspected. None of the successful
searches gives the strict closed comparison with its augmentation. Project `rg`
searches for strict reduction/projection, simultaneous reduction and this node id
in lean/WeilConjectures and lean/Sheaf found no exact duplicate. The single-derived
closed tensor projection and generic quotient-system projection lift were read:
they do not state the asserted isomorphism in actual derived systems. The sequence
site and CoefDerivedSystemEvaluationCalculus were reused. Its reduction model has
normalized finite evaluations but no universal simultaneous ordinary reduction
counit/augmentation interface needed to specify this comparison. The new definition node owns that presentation interface; the original tower
record is retained unchanged.

## New nodes

`def-sf-integral-strict-reduction-model` owns the existing sandbox model module
under §1(A); it does not replace or repair the tower-in-D(B) node. Its statement
spells out every field: ordinary functor, evaluation isos and quotient transition
equation, augmentation section equation, ordinary limit adjunction and its
projection equation, universal derived counit, good-complex computation, and
normalized derived evaluations. Its statement dependencies include the existing
sequence site and unchanged tower node, plus the flat-term K-flat predicate and
finite computation definitions. There is no existence claim or choice of data
from an unproved existence theorem. The old helper existence theorem is removed.
The source is the item's simultaneous reduction obligation in the current
localization blueprint, with Stacks 06YY/06XN/0941 for the universal formulation.
`CoefficientDerivedSystemReductionModel` and `CoefficientDerivedSystemReduction`
were read in full: they already provide reduction, its limit adjunction, evaluated
computations and strict representatives. They do not provide an ordinary functor
T and a universal cochain counit Q R → T_complex Q. That extra presentation is
needed by the accepted `IsProjectionNormalized` equation to fix the actual
system-level map through simultaneous resolutions. The new record supplies that
presentation, not a second category of systems or a second finite reduction.

`def-sf-projection-coefficient-direct-image` is an existing:true ownership record for
`IntegralAmbient.coefficientMap` and `IntegralAmbient.push` in the published
IntegralAmbientOperationModels module. The statement specifies the completed
coefficient map by every finite projection and the ordinary module pushforward
with precisely this scalar action. Source: Stacks 03D2/03D7 and the inverse-limit
coefficient construction. The main ambient comparison theorem is not used as a
statement input. Searches found the general Mathlib pushforward but no earlier
node owning this specialization; def-sfb-integral-ambient-direct-image-encoding
is finite/ambient encoding data, not this direct-image functor. The similarly named landed
def-sf-completed-module-direct-image owns CompletedTowerDirectImage for a
supplied adic datum rather than the precise IntegralAmbient interface with
independent universes. It is retained unchanged, and this node has a distinct id.

`def-sf-finite-reduction-computation` is an existing:true ownership record for
`coefficientOrdinaryQuotient` and `coefficientFiniteReductionModel` in the published
CoefDerivedSystemEvaluationCalculus module. It gives the actual ordinary quotient
mate and the normalized finite K-flat computation obtained from the universal
scalar-extension counit. Source: Stacks 06YY/0941. These data are read directly;
no simultaneous evaluation-calculus theorem is a statement assumption. Existing
`def-pur-coefficient-reduction-presentation` owns a predicate using these maps,
not the maps themselves. Existing finite-system definitions use different sites
or restricted inputs. The new record states only the precise reused maps.

`def-sf-constant-tower-square` is an existing:true ownership record for
`StrictReduction.constantSquare`. Source: the ordinary functor-category
construction used in the localization obligation. Each component is identity on
F(M); the direction is the inverse of Mathlib's Functor.compConstIso. It owns no
derived comparison theorem. `def-sf-strict-tensor-reduction-termwise`, already
landed, is reused for termwise and its finite-limit/colimit preservation instances.

For each new node, LeanSearch, LeanFinder or Loogle, Mathlib grep and project/node
searches are recorded in mathlib_searches. Project searches reused the existing
maps; none is copied into a new source module. Blueprint ancestor was checked by
blueprint_refs.py: prop-sf-localization-all-stages. The new records cite exactly
their bracketed dependencies. Each new node is a direct statement dependency of
the item. The node graph remains directed toward the original tower and sequence
site; neither original node is made dependent on the new model.

## Returned delivery repairs

F1 (H13/H4): restored the base Q28 existing:true record of
`def-weil-integral-reduction-tower` byte for byte. It remains a tower in D(B) and
its roughly 97 citers retain their interface. The new model has its own §1(A)
node. Its blueprint markers now name that node. The unused existence theorem
was removed, so the new definition makes no postponed theorem claim. Existing
CoefficientDerivedSystemReduction was compared as described above. This eliminates
the reported reverse dependency and cycle; no library source was changed.

F2 (H2): removed the three theorem nodes
`lem-coef-derived-system-evaluation-calculus`,
`lem-pur-integral-ambient-operation-models` and
`lem-weil-pbc-reduction-pullback-derived-tower` from the item's added statement
dependencies. The base dependency set is preserved. Their actual definitions are
now cited through the new ownership nodes and the existing termwise definition
node. The flat-term K-flat predicate is likewise explicitly owned by the already
landed def-a1-flat-term-kflat-complex. The accepted main theorem and all its
normalizations are unchanged. Public imports still expose the original modules
because that is where the definition-owned declarations live.

## Second reading by Q66

No second worker was started, as the dispatcher explicitly forbids it. The
maintainer's independent review is the independent reading under the current
worker-direct-delivery protocol. My own clause-by-clause rereading checked the
node and both files, with attention to possible phantoms: evaluation alone cannot
specify the system comparison. This led to the universal derived counit and the
whole-system representative equation in IsProjectionNormalized. Another check
moved ExactImages from a possible theorem premise into the existential conclusion.
The augmentation is likewise normalized BEFORE evaluation. No statement dispute
or source correction remains.

Repair validation: both delivered modules are compiled separately by scompile.py;
the delivery wrapper performs current-main refresh, ownership preflight and probes
of every existing:true declaration. No direct Git operation is performed.
