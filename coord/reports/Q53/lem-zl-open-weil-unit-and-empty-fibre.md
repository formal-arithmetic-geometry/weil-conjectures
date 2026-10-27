## Worker report

Q53 states `WeilConjectures.ZlOpenUnit.openWeilUnitAndEmptyFibre` in
`Sheaf.Paper.ZlOpenWeilUnitEmptyFibre`. This is a statement-only delivery:
`rationalAlpha_natural` and the main theorem have `sorry` proofs. Every definition
has explicit data; the former theorem supplies only the naturality proof of a
specified componentwise isomorphism. All helpers concern clauses of this node.
The H2 repair adds definition-node ownership for five existing ordinary-open and
identity-image constructions; their Lean source remains the published source.

Hypotheses and clauses, in node order:

- The finite-field datum is `D : FiniteFieldDatum.{u}`. The coefficient prime is
  `l` with `[Fact l.Prime]` and `hl : l ≠ D.p`. The chosen algebraic closure is
  `Ω : Type u` with `[Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]`, the
  existing `FiniteFieldDatum.CoefficientDatum` size convention.
- `X₀ U₀ : Over (Spec (.of D.k₀))` with `LocallyOfFiniteType`, `QuasiCompact`,
  and `IsSeparated` structural maps give exactly separated finite-type models.
  `j₀ : U₀ ⟶ X₀` with `[IsOpenImmersion j₀.left]` is the given open. The
  existing `zlFiberMap D j₀` is its geometric base change, not a new morphism.
- `integralJ`, `rationalJ`, and `Action` use exactly the compactification
  `Compactification.ofIsOpenImmersion (zlFiberMap D j₀)` and the recorded
  `sfCompactSupportFiniteIntegralFunctor`, `sfCompactSupportFiniteFunctor`, and
  `SfCompactSupportCoefficientAction`. No derived category of Weil pairs is used.
- `IntegralData`, `RationalData`, and `CommonData` instantiate `OpenData` on the
  actual integral, rational and common-stage constructible categories, actual
  pullbacks and geometric Frobenius pullbacks. `integralAlpha`, `rationalAlpha`,
  and `zlFrobeniusSquare` are the prescribed pullback compositors along the
  geometric Frobenius naturality equality.
- `OpenData.adj` is `J ⊣ P`; `unit_iso` makes the natural unit invertible.
  `IntegralUnitNormalization` fixes that unit to the actual ordinary open unit
  through `frameworkOpenPullRealization` and `integralOpenRealization`. The latter
  is the inverse recorded Roos support realization followed by the normalized
  removal of the proper identity factor. Thus the integral unit is specified.
- `OpenData.beta` has Lean direction `J ⋙ GX ≅ GU ⋙ J`, i.e. mathematical
  `G_X J ≅ J G_U`. `mate` fixes its inverse as the adjunction transpose of
  `G_U(eta)` followed by alpha. This is the canonical open base-change mate;
  transporting the completed exchange gives the same transpose. It is not an
  arbitrary isomorphism between the two functors.
- `OpenData.normalized` is exactly the displayed equation: `GU.map eta ≫
  alpha.hom.app (J.obj K) ≫ P.map beta.hom = eta` at `GU.obj K`.
- `IsoAlgebra.mapOfNatIso beta` is the functor on fixed pairs whose structure
  is beta followed by `J.map theta`. `WeilUnit` asserts a natural Weil
  isomorphism to its restriction, with underlying hom exactly `adj.unit` and
  underlying inverse exactly the inverse of that same natural unit.
- `Rationalization` fixes the actual unit and beta after the recorded raw
  localization. Its `HEq` statements only accommodate the explicit presentations
  of those unchanged localized objects; they assert equality of the arrows.
- `FiniteScalarCompatibility` uses the prescribed integral transition functors,
  integral pullback scalar comparisons and `S.integralBeta`. Rational comparisons
  are the recorded `rationalPullbackScalarComparison` conjugated by the specified
  `operationStageTransitionIso`; the support edge is exactly `S.system.β`,
  conjugated by `S.finite_eq`. `ScalarLaws` writes both actual commutative squares
  for eta and beta. Inversion gives the square for the inverse unit. Functoriality
  transports the normalized equation, so no separate finite-reduction equality
  is substituted for equality of integral maps.
- `CommonStageCompatibility` uses the actual inclusions of literal finite
  stages, their specified object identifications `localQbarPullbackStageIso`,
  and `S.system.ιCompFunctorIso`. It requires the same two scalar squares.
- `EmptyFibre` quantifies over every `x : Spec k ⟶ X` satisfying the literal
  disjointness of its range and the open range. It asserts `IsZero` of the
  actual integral derived pullback for every integral constructible K, actual
  rational pullback for every rational K, and actual common-stage pullback for
  every common-stage K. The integral full subcategory is tested through its
  ambient `.obj`, which is equivalent to being zero in the full subcategory.
  Being zero supplies the unique isomorphism to zero, natural in K and compatible
  with scalar extension; there is no choice of a zero identification to track.
- Its last two conjuncts assert `IsZero` in every degree `a : ℤ` of the recorded
  coefficient point complexes `localPointComplex` and `localQbarPointComplex`
  for the extended Weil pair, using exactly `coefficientFdCohomology` and
  `coefficientQbarCohomology`. These are all stalk cohomology groups in the node's
  convention, rather than merely the degree-zero stalk of a heart object.

Dependency declarations used (full signatures and docstrings read):

- Mathlib `AlgebraicGeometry.IsOpenImmersion`, `LocallyOfFiniteType`,
  `QuasiCompact`, `IsSeparated`, `quasiCompact_of_noetherianSpace_source`.
- `Sheaf.Paper.SfWeilSheafComplex`: `sfWeilComplex`,
  `sfCommonStageWeilComplex`, `sfWeilFrobeniusPullback`,
  `sfCommonStageWeilFrobeniusPullback`, `sfWeilPrimeInvertible`.
- `Sheaf.Paper.DerivedPullbackTensorHom`: `constructibleIntegralPullback`,
  `rationalDerivedPullback`, `commonStageDerivedPullback`,
  `integralPullbackScalarComparison`, `rationalPullbackScalarComparison`,
  `operationStageTransitionIso`.
- `Sheaf.Paper.QcqsCompactSupportRealization`: `sfQcqsCompactSupportRealization`;
  its reexports give the specified integral compact-support operation.
- `Sheaf.Paper.CompactSupportCoefficientAction`:
  `SfCompactSupportCoefficientAction`, `sfCompactSupportFiniteFunctor` and its
  specified integral and rational scalar comparisons.
- `Sheaf.Paper.LocalFrobeniusTrace`: `localPullbackComposition`,
  `localQbarPullbackStageIso`, `localPointComplex`, `localQbarPointComplex`.
- `Sheaf.Paper.WeilIndSheafCategory`: `zlFiberMap`, `zlFrobenius_naturality`,
  `zlFrobeniusSquare`, `zlIntegralPullComp`. Its existing node is added to stmt_deps for these helpers;
  its ind-category operations are not substituted for the constructible categories.
- `Sheaf.Paper.IntegralSupportFunctorNormalization`:
  `IntegralSupportNormalization.ordinaryOpen`, `openIdentity`. The new existing-declaration node
  `def-zl-ordinary-open-support-normalization` owns these constructions and their
  identity-image helpers. The theorem node
  `lem-sf-integral-support-functor-normalization` is not a statement dependency.
- `Sheaf.Paper.ZlFrameworkOpenExchange`:
  `ZlFrameworkPbc.frameworkOpenPullRealization`. Its existing node is added to
  stmt_deps for the quotient-unit-normalized endpoint realization.

All added definition dependencies were checked through both statement and proof
edges: none reaches the item or the new definition node. The seven-step proof in the main theorem's
source docstring records the completed exchange, strict Roos restriction,
coefficient passage, Weil-arrow calculation and empty-site argument. The
latest blueprint Part 2 extension-by-zero sentence was read. No statement
correction or disputed assertion was found.

Edge cases checked before and after elaboration: U empty (all source objects
and extensions zero); U=X and identity open (the unit is the normalized identity,
and no disjoint point exists); K=0; any cohomological degree, including negative
degrees; points need not be immersions or k-linear Frobenius-fixed points;
Frobenius itself is not assumed k-linear. Scalar inclusions include equality of
fields. Common-stage objects and morphisms retain their literal finite stages.

Searches for an existing exact statement:

- msearch leanfinder, `normalized Weil open unit empty geometric fibre extension
  by zero`: eight unrelated normalization/basic-open hits, no exact statement.
- msearch leansearch, `Open extension by zero has an invertible restriction unit
  compatible with Frobenius and a zero derived fibre outside the open`: eight
  Finsupp, ringed-space restriction and ordinary module-restriction hits, none
  giving the completed coefficient-stage assertion.
- msearch loogle, `"IsoAlgebra", "adjunction"`: OK, zero hits. An earlier query
  `IsOpenImmersion, DerivedCategory, extension by zero` was rejected as syntax;
  the valid quoted-name query supersedes it.
- msearch grep, `openImmersionLowerShriek` in CategoryTheory: zero hits.
- rg in `lean/WeilConjectures` and `lean/Sheaf` for the item id,
  `openWeilUnitAndEmptyFibre` and `EmptyFibre`: no existing declaration.
  Searches for open adjunction, open exchange, Frobenius comparison, coefficient
  pullback and normalization found the interfaces reused above; none states
  this combined unit and arbitrary-complex empty-fibre statement.

## Second reading by Q53

The dispatcher requires this worker to deliver directly and expressly prohibits
starting other agents; the maintainer performs the independent delivery review.
I reread the node and final file clause by clause within this session. The
self-audit fixed the inverse-unit presentation (inverse of the full natural
unit, rather than requesting an unbound component instance), supplied the
Noetherian/quasi-compact base-change instances, and matched the existing
coefficient-datum universe convention. It also added the actual scalar unit and
beta equations at finite stages and under literal-stage inclusions. This is a
self-audit, not a claim of independent review by a second worker.

Validation of the returned head (superseded by the repair validation below):
`scompile.py Q53 lem-zl-open-weil-unit-and-empty-fibre` compiled the
final file cleanly both as `Sheaf.Stage2.Sandbox0` (56.9 s) and as
`Sheaf.Paper.ZlOpenWeilUnitEmptyFibre` (59.9 s). No diagnostic commands, profiler
options, or unexpected warnings remain. The specified helper
`rationalStageScalar` packages the recorded scalar square with an explicit result
type to avoid repeating expensive elaboration; it constructs exactly the
transition conjugation described above.


## Returned delivery repair

Independent review of immutable head `056e8c681433` returned one blocking point,
H2: the statement cited the theorem node
`lem-sf-integral-support-functor-normalization` only for plain constructions in
its source module, without using its theorem conclusion. This is repaired by
replacing that dependency with the new definition node
`def-zl-ordinary-open-support-normalization`, whose `existing: true` record
lists exactly `ordinaryOpen`, `identityModuleImage_existsUnique`,
`identityModuleImage`, `identityImage` and `openIdentity` in the unchanged
published module `Sheaf.Paper.IntegralSupportFunctorNormalization`.
The helper existence theorem specifies a unique isomorphism on every section;
its choice therefore satisfies the no-hollow-definition rule. No theorem
conclusion is smuggled into the item's assumptions, and no helper is copied.

The first advisory is addressed by using the existing named
`zlIntegralPullComp` instead of directly selecting
`integralPullbackComposition.choose` in the two occurrences of `integralAlpha`.
It unfolds to exactly the same normalized comparison. The second advisory is
addressed by citing `def-pur-integral-compact-support-coefficient-data` for the
completed system and adding its module as a direct public import. I also cite
`def-sp-open-coefficient-adjunction-data`, which is the current recorded owner
of `PurCompactSupport.pull`, `openExtension`, and `openDerivedAdjunction` in
that module, as well as citing both owners in the new definition node.

The sandbox was compared to current main: main still has no Lean record or
module for the item; apart from `lean`, its node differs only by the permitted
additional statement dependencies. The delivery wrapper rebases the repair onto
current main. The item's natural-language statement, theorem signature and all
its mathematical clauses are unchanged from the independently checked head.
All dependency closures were checked for cycles. Edge cases U empty, U=X, K=0,
and identity coefficient inclusion remain as in the accepted mathematical review.

## New nodes

`def-zl-ordinary-open-support-normalization` records the existing ordinary
integral open extension and the section-normalized identity direct image, its
unique-characterization helper, its derived comparison and removal of the
identity proper factor. The source is Stacks 03D8, 03DI and 03DJ (read in
`literature/stacks-project/sites-modules.tex`) and the latest blueprint's
Part 2 extension-by-zero sentence. Its statement introduces arbitrary schemes,
the prime and finite coefficient extension, the actual completed coefficient
system and the ordinary module derived categories. It characterizes the inverse
module comparison on every pro-etale section by restriction along the canonical
identity base-change map, then explicitly derives that comparison and whiskers
it with open extension. These clauses render exactly the five existing
constructions. It does not assert the separate constructibility/completeness
normalization theorem. The node's `lean.statement` is the verbatim
`openIdentity` signature from the published source.

The required searches found existing Lean constructions but no definition-node
owner: LeanSearch returned eight generic identity/direct-image hits;
Loogle for `"rightDerivedFunctorIsoMapDerivedCategory"` returned zero;
msearch grep of CategoryTheory returned zero; rg of Mathlib, WeilConjectures,
Sheaf and the DAG found the five exact project declarations attached only to
the theorem node. `blueprint_refs.py search "ordinary open identity direct image
normalization"` found zero blueprint nodes. Their exact outputs and queries
are recorded in the new node's mathlib_searches. The old blueprint docstrings
on these reused declarations remain unchanged, as for other existing-declaration
ownership records; the new node's record explains the H2 re-export.

## Repair second reading by Q53

I reread the new definition against all five published bodies and the item's
normalization composite. The comparison direction is
`image (j,id) ≅ ordinaryOpen`, and the inverse module comparison on sections
is restriction along the map from the identity base change to V, as in the
source signature. Right deriving it and using the right unitor gives exactly
`openIdentity`. No new implementation or missing uniqueness assumption was
introduced. The theorem dependency has been removed; the actual definition
owners have been added. This is an author self-check; the dispatcher still
prohibits additional agents and the maintainer independently reviews delivery.

Repair validation: the prescribed scompile.py wrapper accepted the changed item
both as a sandbox module and under its actual library name, with no compiler
errors or unexpected warnings. deliver2.py --no-push also compiled the
existing-declaration check for all five helper declarations and printed
`OK (dry run): commit 7a6e4de9f22 passes the preflight and compiles`.
No additional Lean file is supplied for the existing-declaration definition node.
