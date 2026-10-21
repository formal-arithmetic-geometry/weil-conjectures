## Worker report

Delivered `Sheaf.Paper.PerAdicCommonStageTruncations`, primary theorem
`AlgebraicGeometry.Scheme.perAdicCommonStageTruncations`, with one `sorry` and no
postponed definition data. `CategoryTheory.StageSystem.AdicCommonStageTruncations`
is a record of the assertion's witnesses and equations, not a new coefficient category,
functor construction, or independent mathematical notion. Its generic parameters avoid
repeated unfolding of the concrete coefficient categories. Only the theorem asserts
that this record is inhabited; no object is defined by choosing from that assertion.

Hypothesis correspondence:

- `k : Type u`, `[Field k]` render the arbitrary base field.
- `l : ℕ`, `[Fact l.Prime]`, `_hl : IsUnit (l : k)` render the invertible prime.
- `Ω : Type v`, `[Field Ω]`, `[Algebra (Padic l) Ω]`,
  `[IsAlgClosure (Padic l) Ω]` render the fixed algebraic closure. Its universe is
  independent of the scheme universe.
- `X : Scheme.{u}`, `[X.Over (Spec (.of k))]`, `IsSeparated`,
  `LocallyOfFiniteType`, and `QuasiCompact` on its structure morphism render exactly
  a separated finite-type k-scheme. The existential Noetherian, dimension and stalk-unit
  instances are conclusions of finite-type geometry, not extra hypotheses.
- Finite fields, valuation rings, chosen uniformizers, positive quotient towers and
  completed pro-etale coefficients are those inside `pbcStageCategory`,
  `pbcIntegralStage`, `pbcStageLocalization` and `pbcScalarSystem`. These use the
  existing `pbcFiniteField` small models; no universe equality or new coefficient
  presentation is assumed. The PBC integral predicate retains uniform constructibility
  and compatible etale-origin witnesses, and rationalization is raw tensor-Hom
  localization. No Karoubi envelope and no Tor-compatibility premise are used.

Clause correspondence (fields refer to `AdicCommonStageTruncations`):

- The final two quantified equivalences of the theorem fix `d.finite E` at every
  cutoff to exactly the integral standard half's isomorphic rational image. This is
  the recorded localized standard structure on the already published normalized
  shift and integral-image triangulation; `finite_bounded` gives its boundedness.
- `scalar_tExact` renders t-exactness of each actual pair-system tensor transition
  `S.T h = pbcScalarExtension ... h`. This is the completed finite tensor functor,
  normalized to literal identity at repeated fields. `S.assoc` is exactly
  `pbcScalarAssociator`, not an arbitrary comparison. The separately recorded
  `pbcCoherentScalarExtension` uses unshrunk coefficient fields in the scheme
  universe; here the pair node's canonical small-model realization is used, so
  no closure-universe restriction is silently imposed.
- `upper`/`lower` are natural isomorphisms for both truncations. `upper_counit` and
  `lower_unit` give the characterizing canonical-map normalizations.
  `upper_id`, `lower_id`, `upper_comp`, `lower_comp` give the identity and exact
  associator composition equations.
- `cohomology` is a natural comparison for H^r, realized as H^0(K[r]) in the
  derived category through the existing `homology₀` and full heart inclusion.
  `cohomology_normalized` is precisely the two degree-zero truncation comparisons
  followed by the published scalar shift comparison; `cohomology_id` and
  `cohomology_comp` give its identity and associator equations. This is the same
  ordinary standard cohomology as (τ≥r τ≤r K)[r], not perverse cohomology or
  global hypercohomology.
- `common`, `common_bounded`, `common_le`, `common_ge`, `common_heart` give the
  bounded common-stage standard t-structure and the isomorphism closures of the
  finite halves and hearts. `d.common = pbcQbarStandardT l Ω X` explicitly reuses
  the published standard t-structure from the cohomology dependency's companion
  module, rather than defining a second one.
- `truncUpper_obj`, `truncLower_obj` give literal `(E, τ_E K)` object formulas.
  `truncUpper_map`, `truncLower_map` quantify over EVERY representative and give
  `[M, c_source ≫ τ_M(u) ≫ c_target⁻¹]`. The left hand side is a functor on the
  existing quotient Hom, so the formula simultaneously asserts independence of
  representatives and the identity/composition laws. `HEq` only handles the
  displayed object equalities; it does not change the quotient relation.
- `canonicalUpper`, `canonicalLower` identify these actual functors with canonical
  truncations. `canonicalUpper_counit`, `canonicalLower_unit`, `cutoff_upper`, and
  `cutoff_lower` give the classes of the finite-stage units, counits, and cutoff
  maps. Equations among these canonical maps therefore descend at common stages.
- `truncation_triangle` identifies the COMPLETE canonical common-stage triangle
  with the mapped finite-stage triangle: middle component is identity, first and
  third are the already fixed canonical comparisons. Its triangle-isomorphism
  type includes the shifted boundary square and distinguishedness follows from
  the published exact stage inclusion, not from an arbitrary cone choice.
- `common_cohomology` is a natural inclusion/cohomology comparison in every degree,
  yielding H^r(E,K) ≅ (E,H^r_E K). `heart_enlargement` finds one N containing the
  ORIGINAL coefficient field, puts the actual transported K in its finite heart,
  and identifies Z with that object's H^0 included from N. The upper and lower
  heart witnesses need not initially use the same field.

Dependency interfaces read and used:

- Scheme properties: the node is expressly a collector with no declaration. The
  Mathlib Over/morphism-property instances render its named constituents.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`,
  `Padic.finite_coefficientExtensionRing`, together with the inherited actual
  coefficient constructions.
- `Sheaf.Paper.AdicCoefficientDatum`, `Scheme.completedReductionTower` and the
  continuous completed coefficient data used by the integral stage.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`, `Scheme.ProEt` and its topology.
- `Sheaf.Paper.IntegralUniformCoefficient`, `Scheme.pbcBoundedConstructibleComplete`,
  and the existing core `PbcBoundedConstructibleComplete` specialized by
  `pbcIntegralStage` (same predicate with the published small coefficient model).
- `Sheaf.Paper.PbcRationalCategory`, `PbcRationalDerivedCategory`,
  `PbcRationalCategory` and `pbcRationalization`, specialized by `pbcStageCategory`.
- `Sheaf.Paper.LocalizedTStructure`, `pbc_localized_tstructure`: its two image
  classes specify the finite structures in the conclusion. The pair stages have
  their already normalized shift, so the statement uses those classes rather
  than silently identifying two HasShift instance data.
- `Sheaf.Paper.IntrinsicQbarCategory`, with its live eight-declaration record
  unchanged. It publicly imports `Sheaf.Paper.PbcQbarCategory`; the item uses the
  reexported `pbcQbarCategory`, `pbcQbarScalarAction`, `pbcQbarLinear`, and
  `pbcQbarTriangulated`. No dependency-record replacement is required.
- `Sheaf.Paper.PbcScalarExtension`, `pbcCoherentScalarExtension`, and the pair's
  concrete small-model functors/associators from `FiniteStagePairCategory`.
- `Mathlib.CategoryTheory.Triangulated.TStructure.Basic/Heart/TruncLTGE`,
  `TStructure`, `bounded`, `heart`, `truncLE`, `truncGE`, and canonical triangles;
  `WeilConjectures.CategoryTheory.Triangulated.TStructure.Homology`, `homology₀`;
  `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`,
  `DerivedCategory.homologyFunctor` for the ambient cohomology convention.
- `Sheaf.Paper.PbcQbarStandardCohomology`, `pbcQbarStandardT`, the already published
  specialized common-stage standard structure belonging to the cohomology node.
- `Sheaf.Paper.FiniteStagePairCategory`, `pbcScalarSystem`, `pbcScalarExtension`,
  `pbcScalarAssociator`, and `StageSystem.PairCategory.mkHom`;
  `Sheaf.Paper.CommonStageCalculus`, its normalized shift data (owned by
  `def-per-common-stage-shift-structures`, not supplied by the theorem);
  `Sheaf.Paper.PbcVerdierAxioms`, `pbcVerdierAxioms`. The existing finite-stage pair definition, the new definition attachment to
  the normalized structure data, and the genuine Verdier-axioms theorem are
  explicit statement dependencies. `commonStageCalculus` remains available for
  the proof; it is not used as a theorem premise furnishing these definitions.

All stated proof-dependency modules are imported, including finite-type geometry,
IntegralTStructure, FiniteFreeCompletedScalarComparison, DerivedChangeOfRingsCochainModel,
FiniteFreeConstructibleScalarTransport, TExactTruncationComparison, and the upstream
TriangleMorphismExtension. The theorem docstring includes the node's entire nine-step
proof and its citations.

Edge cases checked: X empty (all bounds vacuous, the existential dimension bound is
still available); zero complexes; r=0 and negative cutoffs; E=F and repeated fields
(identity comparisons are explicitly HEq to identity); a point over an algebraically
closed field; distinct fields for the two heart witnesses; maps represented at different
stages; closure and scheme in different universes. None is excluded by the statement.
The quotient formula has comparison followed by τ(u) followed by inverse comparison,
which is the correct orientation for Lean's left-to-right composition.

Searches made with the prescribed msearch.py wrapper:

- `grep` query: adic.*truncation|scalar.*TExact|commonStage.*trunc. Result: 0 hits; . No exact theorem matching all clauses.
- `leanfinder` query: Finite scalar extension of completed adic coefficients is t-exact and truncations descend to the finite-stage pair category. Result: 8 hits; AdicCompletion.map_exact, AdicCompletion.ofTensorProduct_surjective_of_finite, AdicCompletion, IsAdicComplete, AdicCompletion.coe_ofTensorProductEquivOfFiniteNoetherian, AdicCompletion.ofTensorProduct_bijective_of_finite_of_isNoetherian, AdicCompletion.ofTensorProductEquivOfFiniteNoetherian_apply, IsAdicComplete.StrictMono.of_lift. No exact theorem matching all clauses.
- `loogle` query: CategoryTheory.Triangulated.TStructure, CategoryTheory.Functor. Result: 12 hits; CategoryTheory.Triangulated.TStructure.truncGE, CategoryTheory.Triangulated.TStructure.truncLT, CategoryTheory.Triangulated.TStructure.truncGELT, CategoryTheory.Triangulated.TStructure.truncLTGE, CategoryTheory.Triangulated.TStructure.triangleLTGE, CategoryTheory.Triangulated.TStructure.triangleLTLTGELT, CategoryTheory.Triangulated.TStructure.truncGEπ, CategoryTheory.Triangulated.TStructure.truncLTι. No exact theorem matching all clauses.
- `leansearch` query: A filtered union of coefficient categories has a t-structure and t-exact scalar extension commutes with truncations. Result: 8 hits; CategoryTheory.Triangulated.TStructure.mk, CategoryTheory.Triangulated.TStructure.ge, DerivedCategory.TStructure.t, CategoryTheory.Triangulated.TStructure, CategoryTheory.Triangulated.TStructure.noConfusionType, CategoryTheory.Triangulated.TStructure.ge_of_isGE, CategoryTheory.Triangulated.TStructure.ge_shift, CategoryTheory.Triangulated.TStructure.truncLT. No exact theorem matching all clauses.

Direct `rg` in `lean/WeilConjectures` and `lean/Sheaf` for the item id,
`commonStage.*trunc`, `pbc.*TExact`, and ordinary/common-stage t-structure names found
the general t-exact comparison infrastructure and the already published
`PbcQbarStandardCohomology` standard structure, reused above, but no statement of
finite t-exactness with the full coherent representative/triangle/heart package.
Upstream name-index search found no collision with either delivered declaration.
The source Bhatt--Scholze PDF pp. 60–62 was read (6.8.11 and 6.8.14), as was the
current main-20261015 smooth-pullback blueprint unit. No statement correction and
no STATEMENT-DISPUTED issue.

## Repair of the independent return

H13: restored `def-weil-pbc-qbar-category.json` byte-for-byte from the live read
clone, including NM's `IntrinsicQbarCategory/intrinsicPbcQbarCategory` attachment
and all eight declarations. Its public import of `PbcQbarCategory` already exposes
the legacy PBC interface used by this item. No source change is necessary and
none of the landed citers named by the return is changed:
`def-wf-middle-extension`, `def-fd-coefficient-comparison-datum`,
`lem-per-adic-lisse-cohomology-calculus`, `lem-per-tate-twist-lisse-line`, and
`lem-per-adic-heart-pullback-fibres` retain the identical dependency attachment.

H2: added `def-per-common-stage-shift-structures`, an `existing: true` definition
attachment to the six named CommonStageCalculus constructors and
`qbarPairPretriangulated`. The item now cites it instead of adding
`prop-weil-pbc-common-stage-calculus` to its statement dependencies. Its original
proof use of that proposition is retained. The genuine
`thm-weil-pbc-verdier-axioms` statement dependency is retained: its first conjunct
supplies the pair `IsTriangulated` assertion. The item Lean module is unchanged.

The advisories concern existing dependency interfaces and the accepted assertion:
`pbcQbarStandardT_existsUnique` is not introduced or chosen from anew here;
`common_cohomology` states existence of the comparison as in the reviewed packet.
The second reading below is explicitly a self-check. The dispatcher forbids other
agents and assigns independent review to the maintainer.

## New nodes

`def-per-common-stage-shift-structures` owns the existing normalized rational
shift, rationalization/scalar shift comparisons, pair shift, inclusion comparison,
pair zero-object and pair pretriangulation data. Its source is the current
blueprint common-stage-calculus definition paragraphs and the common-stage cone
predicate. Mathlib LeanSearch/Loogle/LeanFinder return general shift interfaces,
not these normalized coefficient constructions. Direct DAG and blueprint searches
find no definition node owning this data; the old theorem nodes contain the
implementations among their auxiliaries. Direct source search finds the exact
seven constructors, so the new node reuses them with `existing: true` and introduces
no Lean file, declaration, or postponed theorem. The record's module
`PbcVerdierAxioms` publicly exposes all seven: six through `PbcCommonStageCones`
and `CommonStageCalculus`, and `qbarPairPretriangulated` in its own source.
The node binds the same prime, closure, scheme and source-domain hypotheses as
the published specialization; independent closure/scheme universes remain allowed.
It adds data ownership, not a mathematical strengthening of the item.

Repair searches (2026-10-21), recorded with their actual results in the new node:

- LeanSearch: normalized integer shifts on localized adic categories: eight generic
  localization/shift hits, including `HasShift.localized`.
- LeanFinder: shift on filtered union with representative comparisons: eight
  generic t-structure shift lemmas.
- Loogle: `CategoryTheory.HasShift, CategoryTheory.Functor.CommShift`: twelve
  generic shift-comparison declarations.
- Mathlib grep for the four representative constructor names: zero hits.
- `rg` in `WeilConjectures`: zero hits for those names; `rg` in `Sheaf` found
  the existing constructors in `CommonStageCalculus` and `PbcVerdierAxioms`.
- DAG `rg` found only theorem nodes and their users; `blueprint_refs.py search
  'common-stage shift'` returned zero blueprint matches. `ancestor` returns
  `lem-per-smooth-pullback-t-exact`, used in the new node's provenance.

## Second reading by NO

The dispatcher explicitly forbids starting another agent, and the prompt assigns
independent review to the maintainer after delivery. This section records a fresh
self-check, not a claim that a second agent has read the packet. I reread the node
against every record field and the theorem binders. This caught two presentation
issues during construction: the concrete category expansions made a monolithic
record exceed the compile limit (fixed by the same generic equations specialized
at the theorem), and the cohomology dependency already publishes a standard
common-stage t-structure (now explicitly reused by equality). I checked all
comparison directions, the original-field containment in heart_enlargement, the
middle identity and prescribed end components in the triangle isomorphism, the
absence of an assumed Noetherian/dimension/Tor premise, and the complete coverage
of all hypotheses and conclusions listed above. No mathematical statement changes
were needed. Independent maintainer review remains the next review step.

Repair self-check: I reopened the restored Qbar record and compared its bytes
with the live node. I read each of the seven constructor signatures and docstrings:
`pbcRationalHasShift` uses the uniquely normalized tensor-Hom shift;
`pbcRationalizationCommShift` has identity components;
`pbcScalarCommShift` descends the integral adjunction-mate comparison;
`pbcPairHasShift` uses the actual representative shift and its finite-stage
zero/addition maps; `pbcStageInclusionCommShift` uses the identity-on-objects
comparison; `pbcPairHasZeroObject` uses a finite-stage zero; and
`qbarPairPretriangulated` uses the uniquely characterized common-stage triangle
predicate. These are data constructors, which is why the new node is a definition.
I checked the new node's right-to-left arrow formula against the existing Lean
left-to-right formula. Repeated stages, zero objects, negative shifts and the empty
scheme keep the original normalization; the coefficient index is nonempty even
when the scheme is empty. The item still contains every clause accepted by the
independent review and has the same theorem signature and module bytes.
