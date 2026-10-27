## Worker report

The delivery states `AlgebraicGeometry.Scheme.purCompletedReductionReindexing` in
`lean/Sheaf/Paper/PurCompletedReductionReindexing.lean`. Its only postponed proof is
that named theorem. The seven preceding definitions contain real constructions or
Prop-valued expansions of the clauses of this one node; none chooses mathematical
data from an unnormalized existence assertion. The theorem docstring carries all
eight proof steps of the DAG argument, including the projection, quotient-unit,
pure-tensor and adjunction-transpose normalizations.

The natural-language node statement, proof and proof dependencies are unchanged.
The statement dependencies gain five already landed nodes whose actual interfaces
are used: def-weil-pbc-bounded-constructible-complete,
def-weil-pbc-strict-tower-operations, prop-weil-pbc-direct-image-limits,
def-weil-pbc-cartesian-square, and def-weil-pbc-ambient-ringed-exchange. No new DAG nodes are introduced.

Hypothesis and clause correspondence:

1. The prime is `(l : ℕ) [Fact l.Prime]`. The finite extension is
   `(E : Type (t + 1)) [Field E] [Algebra ℚ_[l] E]
   [FiniteDimensional ℚ_[l] E]`. The datum is the existing
   `pbcPadicCoefficientDatum l E`: its coefficient ring is exactly
   `Padic.coefficientExtensionIntegers l E`, and its ideal is exactly
   `Ideal.span {Padic.coefficientExtensionUniformizer l E}`. This uses the
   published unlifted coefficient interface, rather than imposing E : Type t.
2. Schemes are `Scheme.{t}`. The existing small pro-etale site retains object
   universe t+1 and morphism universe t. Rings and module values have universe
   t+1. The hypothesis that l is invertible is
   `∀ x : T, IsUnit (l : T.presheaf.stalk x)`, and analogously on Y for the
   square. Pullback carries it to the other schemes of the square. There is no
   nonemptiness, Noetherian-scheme, dimension, boundedness, constructibility,
   etale-origin, compactification, properness, or additional base-linearity
   assumption. The arithmetic ring's Noetherian/perfect/finite properties are
   fields of the actual datum, not added premises.
3. The underlying isomorphism is `(u : T' ⟶ T) [IsIso u]`. No base scheme is
   introduced. `d.completedRing T` is the actual inverse limit of the positive
   finite quotient sheaves, and `d.integralRingIso u` is the canonical
   projection-normalized identification. It is used by `proEtaleRingModulePullback u (d.completedRing T)
   (d.completedRing T') (d.integralRingIso u)`,
   the already published tensor presentation of inverse image with transported
   module action. The operations node identifies that presentation by
   x tensor a ↦ c inverse(a) x, with inverse x ↦ x tensor 1.
4. `PurCompletedReindexingAt` first gives a natural isomorphism from the
   underlying abelian sheaf of this actual module pullback to
   `isoSectionwiseInverseImage u AddCommGrpCat`. Its inverse is explicitly the
   module adjunction unit followed by restriction along
   `proEtaleIsoCommaArrow u U`. At every U this is exactly the distinguished
   inverse-image coprojection identification, so an arbitrary isomorphism of
   underlying sheaves cannot be substituted. This renders the statement's
   relabeling G_u. The completed module action remains that of the existing
   ringed pullback, using `d.integralRingIso u`.
5. The next conjuncts exhibit equivalences on completed modules and strict
   towers whose functors are exactly `proEtaleRingModulePullback u (d.completedRing T)
   (d.completedRing T') (d.integralRingIso u)` and
   `d.towerModulePull u`, and whose inverses are these same canonical functors
   for `inv u`. Preservation of finite limits and finite colimits states
   exactness. The derived equivalences have functors exactly `d.pull u` and
   `d.towerPull u`, and inverse functors for `inv u`. These are the published
   exact termwise localizations, on the entire unbounded derived categories.
   `d.towers T` is ℕᵒᵖ ⥤ Mod(d.completedRing T), with n indexing positive level
   n+1. No independent sequence of derived evaluations is used as a tower.
6. The ordinary natural isomorphism `beta` has type
   `completedTowerLimit T ... ⋙ proEtaleRingModulePullback u ... ≅
    d.towerModulePull u ⋙ completedTowerLimit T' ...`.
   Its equation with `limit.π` at every strict tower C and index n fixes it by
   inverse images of the actual projections. The natural derived isomorphism
   `b` has type `completedRlim T ... ⋙ d.pull u ≅
    d.towerPull u ⋙ completedRlim T' ...`.
   Its equation on every K-injective strict tower complex, with
   `rightDerivedFunctorUnitQ` and `mapDerivedCategoryFactors`, states precisely
   that it localizes beta. Thus this includes the projection-induced
   normalization on resolutions, not just invertibility or projection equations
   in a derived category. The isomorphism itself gives naturality on all
   localized morphisms and all derived strict tower objects.
7. For each `K : d.derived T` with `d.TowerComplete T K`, the isomorphism `e`
   goes from `(d.completedPull u).obj K` to `(d.pull u).obj K`.
   Its inverse is exactly `d.ordinaryToCompleted u K`. The second equation
   `e.hom ≫ (d.pull u).map (d.completionUnit T K) = b.inv.app ...`
   specifies the displayed composite of the inverse limit comparison and the
   inverse quotient-completion unit, without requiring an ad hoc local IsIso
   instance in the signature. TowerComplete is invertibility of that specified
   quotient completion unit. The recorded
   `AdicCoefficientDatum.towerComplete_iff_intrinsic` identifies it with the
   intrinsic Koszul completeness of the node; this is the published
   unit-compatible Koszul-to-quotient comparison, not a new definition of
   completeness. Neither e nor b is selected in a definition using `sorry`.
8. The tensor comparison t_{u,F} is the inverse of the already specified
   `d.reductionTowerPullbackIso u`, with the node's orientation from reduction
   after pullback to pullback of reduction. The conjunct
   `IsCompletedReductionPullbackComparison d u (d.reductionTowerPullbackIso u)`
   unfolds to `StratumReductionFormula`: an equality of actual strict derived
   maps on K-flat representatives, conjugated by the universal reduction
   counits and the exact localization factors. `completedReductionTower` is
   the published diagram-site reduction functor Delta F tensor^L Q. The
   predicate uses that functor, not a newly chosen lift from level evaluations.
9. The explicit section equation for `completedReductionLevelPullbackIso`
   sends the inverse-image unit of `reductionTensorSection ... a x` to the
   tensor of the inverse-image unit of x and the canonical image of a under
   `proEtaleRingDirectImageMap` for the finite coefficient rings. Under the
   section identification of clause 4 this is exactly relabeled x tensor a
   ↦ x tensor a. It is an equation of module-sheaf sections using the
   sheafification tensor unit, not an assertion that every tensor-sheaf section
   is a pure tensor. Consequently module actions are the actual completed
   actions. The last conjunct, for every `a : n ⟶ m` in ℕᵒᵖ, states that the
   two composites with the strict transition agree. The transition is the
   specified `1 tensor reductionCoefficientMap`; together these equations say
   that both composites on a pure tensor give x tensor the quotient image of a.
   In particular this includes P_(n+1) → P_n, identities and all composites.
10. The square clause binds arbitrary p and p', isomorphisms v and g, and just
    the equality `v ≫ p = p' ≫ g`. It concludes existence of a
    `ChosenCartesianSquare` on these exact four arrows, since these
    isomorphisms make the commuting square Cartesian. Thus a chosen Cartesian
    witness is a conclusion, not an extra hypothesis. `PurCompletedReindexingSquare`
    uses the canonical completed coefficient square `purReindexingRingedSquare d sq`, a real structure literal using the completed
    rings, canonical ring identifications, and `d.integral_coherent sq`.
11. `purReindexingModuleMate` is literally `mateEquiv` of its specified
    ordinary pullback square under the canonical ringed module adjunctions.
    Its section equation is the ordinary reindexing comparison: inverse-image
    unit for g, then this mate, equals inverse-image unit for v followed by
    restriction along `purReindexingTestSquare sq.w`. That test-square map is
    the canonical fibre-product pasting identification, built from
    `Over.pullbackComp` and square commutativity. Since g is an isomorphism,
    testing at its base-changed tests covers the whole small site. The
    comparison is invertible, with the inverse given by reverse restriction.
12. `purReindexingDerivedMate` is literally the specified
    `proEtaleAmbientRingedExchange`, with all four canonical coefficient
    isomorphisms and their existing coherence equation. Its K-injective
    equation identifies it with localization of the actual section-normalized
    ordinary mate, using the right-derived units and exact-pullback factors.
    Thus it is the specified reindexing comparison G_g Rp_* → Rp'_* G_v,
    not just an unspecified isomorphism between these functors.
13. `purReindexingTowerModuleMate` is whiskering of that ordinary module mate
    by ℕᵒᵖ, so every transition is retained in its data. The final
    K-injective tower-complex equation identifies the specified diagram mate
    `(purReindexingRingedSquare d sq).exchangeTowerMate` with localization of
    this very strict ordinary map. Its IsIso conjunct is in the derived
    category of actual strict towers. There is no assumption of faithfulness
    of derived evaluation or a choice of a map from its separate evaluations.

Dependency declarations read and used:

- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing`, with the publicly retained integer
  ring, uniformizer, quotient and transition constructions in CoefficientExtension.
- `Sheaf.Paper.AdicCoefficientDatum`:
  `completedReductionTower`, `completedReductionCoefficient`, `reductionModuleRing`,
  `reductionModules`, `reductionTensorSection`, `completedReductionModuleTowerFunctor`
  and `completedReductionLevel`, all in `AlgebraicGeometry.Scheme`.
- `Sheaf.Paper.IntegralUniformCoefficient`:
  `AlgebraicGeometry.Scheme.pbcPadicCoefficientDatum`, with its actual unlifted ring
  and uniformizer ideal and the already proved arithmetic facts.
- `Sheaf.AlgebraicGeometry.ProfiniteCoefficientInverseImage`:
  `AlgebraicGeometry.Scheme.proEtale_profinite_coefficient_inverse_image`, including
  its projection, transition, identity and composition clauses. The actual datum's
  `integralRingIso` and `projection_comm` use this limit normalization.
- `Sheaf.AlgebraicGeometry.ProEtale.IsoSectionwiseInverseImage`:
  `isoSectionwiseInverseImage`, `isoSectionwiseInverseImage_equivalence`, and the
  publicly retained `proEtaleIsoPostcompose`, `proEtaleIsoCommaArrow` and normalized
  inverse-image identification of ProEtaleIsomorphismInverseImage.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations` publicly retains the general
  `proEtaleRingModulePullback`, `proEtaleRingModuleDirectImage`,
  `proEtaleRingModuleAdjunction`, `proEtaleRingDerivedPullback`,
  `proEtaleRingDerivedDirectImage`, and `proEtaleRingDerivedAdjunction`.
- `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients`:
  `CategoryTheory.ringedStrictTowerHomotopyLimitIndependentCoefficients`; the
  completedRlim interface in CompletedRlimFunctor is the existing actual right
  derived strict limit, with the small site's distinct universes retained.
- `Sheaf.Paper.IntrinsicCompletionCompleted`:
  `IsCompletedIntrinsicallyDerivedComplete`, transported by the existing
  IntrinsicCompletion module; `Sheaf.Paper.CompletedPullback` exports the
  intrinsic/quotient-unit equivalence and the actual completed pullback and unit.
- `Sheaf.Paper.KoszulReconstruction`: `AlgebraicGeometry.Scheme.koszulReconstruction`,
  with its equality of the two canonical units. This is a proof import; the
  existing CompletedPullback transport supplies the comparison on this exact
  small-site, unlifted coefficient presentation.
- `Sheaf.Paper.CompletedCompactSupportExchange`:
  `AlgebraicGeometry.Scheme.completedCompactSupportExchange` publicly retains
  the ordinary and strict completed coefficient constructions used for its
  specified tensor comparison. No compactification is a hypothesis here.
- `Sheaf.Paper.CompletedDirectImageLimits`:
  `completedReductionLevelPullbackIso`, `completedReductionLevelPullbackIso_transition`,
  `IsCompletedReductionPullbackComparison`, and
  `AdicCoefficientDatum.reductionTowerPullbackIso`, with actual tower direct images.
- `Sheaf.Paper.StrictTowerOperations`:
  `StrictTowerRingedSquare`, `.exchangeModuleSquare`, and `.exchangeTowerMate`.
  The local `purReindexingRingedSquare` simply supplies its canonical coefficient
  fields; it uses no pullback-square theorem.
- `Sheaf.AlgebraicGeometry.ChosenCartesianSquare`:
  `AlgebraicGeometry.ChosenCartesianSquare`.
- `Sheaf.AlgebraicGeometry.ProEtaleAmbientRingedExchange`:
  `AlgebraicGeometry.Scheme.proEtaleAmbientRingedExchange`, using its specific
  canonical pullback-composition comparison, not an arbitrary square map.
- Mathlib `CategoryTheory.mateEquiv`, `MorphismProperty.Over.pullbackComp`,
  `CategoryTheory.Functor.mapDerivedCategoryFactors`, and the universal
  localization, exact functor and levelwise abelian functor-category APIs.
  `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback`
  supplies `CategoryTheory.Functor.rightDerivedFunctorUnitQ`.
- Proof imports retain ExactAdjointTowerModels, the independent-universe
  K-injective existence theorem, the independent-coefficient K-flat resolution,
  DiagramSiteRealization, the generic normalized ringed-topos tensor pullback,
  PreDerivedAdjointFunctorsGeneral, and IntegralFinitePullbackComposition.

Edge cases checked before and after writing: the empty scheme is allowed, with
vacuous scheme-level invertibility and no field-level characteristic condition.
There is no nonzero-object or nonzero-coefficient-section restriction. The zero
complex and zero tensor factors have the same normalization. Positive exponent
one is n=0; no P_0 or negative quotient is introduced. Equal indices are included
in the transition equation. Arbitrary unbounded strict tower complexes and
arbitrary derived-complete objects are admitted, with no uniform cohomological
bound. The identity isomorphism and an isomorphism not linear over an unstated
base are admitted. For the square p and p' are entirely arbitrary. Completeness
is used only in the isomorphism from completed pullback back to G_u K. General
site object/Hom universes are never identified.

Searches for an existing exact statement (2026-10-24):

- `msearch.py ... leanfinder "Scheme isomorphism reindexing completed coefficient
  modules strict towers commutes with derived inverse limit"`: eight hits on
  affine-space reindexing and algebraic adic completion; no sheaf/strict-derived
  statement matching this node.
- `msearch.py ... loogle "Functor.IsEquivalence, mapDerivedCategory"`: zero
  hits; the remote endpoint reported `unknown identifier 'Functor.IsEquivalence'`.
  This negative name search was supplemented by semantic and source searches.
- `msearch.py ... grep "mapDerivedCategory.*[Ee]quivalence|[Ii]so.*[Rr]eindex"
  CategoryTheory`: three hits on reindexing limits/products, not this statement.
- `msearch.py ... leansearch "An isomorphism of schemes induces exact equivalences
  of completed coefficient module sheaves and strict reduction towers and commutes
  with derived inverse limits"`: eight results on section isomorphisms,
  underlying scheme homeomorphisms, ordinary algebraic completion congruence,
  and open-immersion module pullback; no matching conjunction or normalization.
- `rg` of WeilConjectures and Sheaf for isomorphism/reindexing/completed-reduction
  patterns, and the literal item id in WeilConjectures: no declaration for this
  item. Existing neighboring modules (IsomorphismDerivedPullback,
  DerivedAutomorphismHomEvaluation, CompletedInverseImageScalarCounit,
  CompletedDirectImageLimits) provide constituent interfaces or constructible
  specializations, not the full unrestricted statement including both mates.
  Those existing objects and comparisons are reused rather than defined again.
- No new independent notion was needed, so no new-definition-node search record
  or blueprint ancestor query is needed.

The current blueprint source was read at
`literature/blueprint/latest/blueprint/sec-six-functors/sk-thm-sf-package/prop-pur-weil-equivariance-compatibilities.proof.md`.
Its constituent-compatibility assertion agrees with the extracted DAG argument.
No mathematical correction or STATEMENT-DISPUTED flag is needed.

Validation before repair: the saved packet passed `deliver2.py --no-push` at
`fd68700c265`. This mechanical pass did not address the independent return.
Final repair validation is recorded below after the server checks.

## Returned points repaired

H13, completed-pullback record: removed the sandbox copy of
`def-weil-pbc-completed-pullback.json`. The delivery no longer touches that node.
Its live `lean` record remains byte-identical, naming
`Sheaf.Paper.PbcQbarCompletedPullback`, Q99's primary declaration, all four of its
declarations, and the existing file. No replacement `existing: true` record is
submitted. `CompletedCompactSupportExchange` already publicly imports
`PbcActualStrictPullback`, which publicly imports `CompletedPullback`; the ambient
`completedPull`, `ordinaryToCompleted`, and `towerComplete_iff_intrinsic` remain
available without rebinding any node or dropping the proved Qbar interface.

H13, plain definitions versus theorem dependencies: removed
`lem-weil-pbc-stratum-completion-unit-restriction` and
`lem-weil-pbc-completed-reduction-pullback-square` from the added statement
dependencies. Replaced every `stratumModulePull` occurrence by its exact defining
`proEtaleRingModulePullback` expression, owned by the existing operations definition
node. Removed the redundant equality to `stratumRlimComparison`; the ordinary
projection equations and the K-injective localization equation still uniquely pin
`b`. Constructed `purReindexingRingedSquare` directly from the canonical completed
rings, their four inverse-image isomorphisms and `integral_coherent`. Its type is
`StrictTowerRingedSquare`, owned by the cited strict-tower-operations definition
node. Imported `StrictTowerOperations` and `CompletedDirectImageLimits` directly.
`prop-weil-pbc-direct-image-limits` remains a statement dependency: the specified
`reductionTowerPullbackIso` is genuinely chosen from that node's uniquely normalized
existence theorem, exactly as the return confirms. No mathematical node text changed.

H11: the earlier section described a self-review and has been removed. The second
reading below is the new repair worker's reading of the retained packet, alongside
the explicitly attributed independent immutable-head review in the return. No
sub-agent was started, as the dispatcher's instruction requires.

## Second reading by Q85

Reader: the separately started Q85 repair worker in this session, reading the saved
packet from the previous worker against the live node, the full Lean module, and
its dependency interfaces. This is a reading of another session's saved statement,
not the original worker's self-review. I also read the independent maintainer review
of immutable head `c53608096b73` supplied verbatim in the return; its mathematical
verdict was “Maths otherwise correct”. The repairs made during this reading are
listed explicitly below; this section does not claim a further agent reviewed them.

- The arithmetic paragraph matches the prime, finite-dimensional Q_l field E,
  and `pbcPadicCoefficientDatum l E`, with its actual integer ring and uniformizer
  ideal. The site has object universe t+1 and morphism universe t, and the field
  and coefficients inhabit t+1; there is no equality of site universes.
- For the scheme isomorphism paragraph, the only geometric hypotheses are `[IsIso u]`
  and invertibility of l on T. The first conjunct of `PurCompletedReindexingAt`
  pins the underlying inverse image through `proEtaleIsoCommaArrow` and the actual
  module adjunction unit. Module and strict-tower equivalences specify reverse
  pullback as inverse, and both finite-limit and finite-colimit preservation.
  Derived equivalences cover unbounded strict towers and modules. I checked that
  expanding `stratumModulePull` changes no functor: its body is exactly the four
  arguments now written at each occurrence.
- For the limit paragraph, `beta` satisfies every tower projection equation and
  `b` satisfies its localization equation on every K-injective tower complex,
  using `rightDerivedFunctorUnitQ` and the exact functor localization factors.
  The dropped `stratumRlimComparison` conjunct was redundant: the retained
  equation determines b by the resolution universal property. Thus no arbitrary
  comparison is admitted. For complete K, e has precisely the two required
  endpoints, inverse `ordinaryToCompleted`, and composite equation with the
  specified quotient completion unit and `b.inv`. `TowerComplete` is equivalent
  to intrinsic completeness by the already proved unit-compatible comparison.
- For the reduction paragraph, the chosen strict comparison is the inverse of
  `reductionTowerPullbackIso`. `IsCompletedReductionPullbackComparison` pins its
  K-flat tensor representative. The section equation uses arbitrary x and a,
  not a claim that all sheaf tensor sections are pure. Every index arrow has the
  transition equation, including identities and all positive quotient levels.
  The two restated dependency clauses are retained because the node itself
  requests these comparison and transition normalizations.
- For the final square paragraph, p and p' are arbitrary; v and g alone are
  isomorphisms, and `v ≫ p = p' ≫ g` is the sole square condition. A chosen Cartesian
  witness is concluded existentially. `purReindexingRingedSquare` supplies exactly
  the completed-ring data and canonical coherence to the existing square structure;
  it introduces neither a new hypothesis nor a choice of comparison. The ordinary
  mate is literally `mateEquiv`, its strict version is whiskering, and the derived
  mate is the specified `proEtaleAmbientRingedExchange`. The section-restriction
  equation uses `Over.pullbackComp` in the required direction. Both derived mates
  have their K-injective localization equations, not merely an IsIso assertion.
- I checked the live Q99 completed-pullback node and its module: all four recorded
  declarations and its module binding are preserved because that node is omitted
  from the delivery. The import path through `PbcActualStrictPullback` retains the
  general completion interface. I also checked that the only remaining newly cited
  theorem dependency, `prop-weil-pbc-direct-image-limits`, supplies mathematical
  data through its normalized existence theorem, rather than a mere plain alias.
- Edge cases remain u=id, the empty scheme, K=0, unbounded/non-Mittag-Leffler strict
  towers, and n=0 representing P_1. No section-nonzero, nonempty-scheme, Noetherian-
  scheme, finite-dimensional-scheme, extra-base, or constructibility hypothesis
  was introduced. The source blueprint constituent-compatibility paragraph agrees
  with the extracted node's scheme-isomorphism use.

Findings and changes: the stale replacement of the Q99 record was removed; the two
plain-definition theorem dependencies were eliminated by the exact module-pullback
expansion and direct canonical ringed-square specialization; the redundant b equality
was removed while retaining its determining K-injective equation. The primary theorem
signature, natural-language statement, proof and proof dependencies are unchanged.
No statement correction or STATEMENT-DISPUTED flag is needed.
