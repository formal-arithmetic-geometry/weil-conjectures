## Worker report

The delivery states `WeilConjectures.dlOpenImageDelta` in
`Sheaf.Paper.WeilOpenImageDelta`, with its whole proof postponed as `sorry`.
The node's statement, source, proof and proof dependencies are unchanged.
The saved work contained the three initially registered modules and node records but
no report. The required initial dry run reported the missing report. I retained
those modules and completed their checks and documentation. The initially unregistered CondensedERealization repair was retained in archive.
The subsequent dry run identified concrete API failures in the published proof
dependency, so that saved repair was restored and registered under its owning node.

Hypotheses and clauses, checked against the node and current blueprint:

- Finite-field datum: `D : FiniteFieldDatum.{u}` contains k0, its specified
  algebraic closure, characteristic p and geometric Frobenius. `l : ℕ`,
  `[Fact l.Prime]` and `hl : l ≠ D.p` are precisely the prime and distinct
  characteristic hypotheses. `Ω : Type v`, `[Field Ω]`, `[Algebra ℚ_[l] Ω]`,
  `[IsAlgClosure ℚ_[l] Ω]` give the chosen algebraic closure of Q_l.
  Scheme and coefficient-closure universes are independent. The convention's
  complex embedding is used for weights; none of this statement's operations
  depends on an embedding, so it is not an additional parameter here.
- Separated finite-type smooth curve and dense open: the theorem quantifies
  over `c : Scheme.MiddleExtensionCurve D`. Its `C` and `U` are schemes over
  Spec k0, with `j : U ⟶ C`, `IsOpenImmersion j.left`, and `DenseRange j.left.base`.
  Its finite-type fields are `LocallyOfFiniteType` and `QuasiCompact` of both
  structure maps, its separatedness fields are `IsSeparated`, and its curve
  fields are `Smooth C.hom` and `C.left.IsPureDimension 1`. For a smooth scheme
  over a field this pure-dimension condition is relative dimension one. No
  connectedness, nonemptiness, properness or geometric irreducibility is imposed.
  Finiteness and separatedness of U follow from the stated dense open in the
  Noetherian curve; recording them in this existing bundle excludes no case.
- Constructible Qlbar Weil sheaves and underlying heart: the inputs and outputs
  use the recorded `sfCommonStageWeilSheaf D l hl X Ω`. These are fixed
  Frobenius pairs in the intrinsic common-stage derived category with carrier
  in `sfCommonStageHeartProperty`; morphisms commute with their Weil maps.
  This is not a derived category of Weil sheaves.
- Lisse short exact inputs: `DlOpenLisseSES.S` is a `ShortComplex` in this
  same Weil heart, `exact : S.ShortExact` expresses 0 -> G1 -> G -> G2 -> 0,
  and `lisse₁`, `lisse₂`, `lisse₃` apply the existing `IsCommonStageLisse`
  predicate to the three geometric carriers. Local finite ranks may be zero
  and need not agree on different components. No global Frobenius-stable
  integral lattice is required. `DlOpenIsLisse` only abbreviates that predicate.
- Ordinary and derived images: ordinary j_* is exactly the dependency's
  `qbarCurveWeilOrdinaryPushforward`. `dlOpenOrdinaryAdjunction` uses its
  specified right-adjoint instance. `dlOpenHigherImage c r` first includes
  the heart into fixed pairs, applies `sfModelWeilDerivedPush c.j`, and takes
  the cohomology functor `sfModelWeilCohomology c.C r`.
  `dlHigherGeometricComparison` identifies its carrier with H^r of geometric
  Rj_* using the uniquely counit-normalized forgetful comparison.
- The theorem supplies one `DlOpenImageData` for every curve-open pair.
  `boundary A` is j_*G2 -> R^1j_*G1. `exact A` is exactly
  `ComposableArrows.mk₄ 0 (j_*.map A.S.f) (j_*.map A.S.g) (boundary A)`
  being exact. It asserts exactness at j_*G1, j_*G and j_*G2, and does
  not assert that the last arrow is surjective.
- Naturality: `DlOpenImageData.naturality` gives the boundary square for
  every morphism of short exact inputs. The other two squares follow from
  the ordinary functor's action. `boundary_formula` identifies the boundary
  with H^0 of the derived image of the connecting arrow of the underlying
  distinguished heart triangle, followed by the specified shift comparison
  and the degree-zero/geometric identifications. Thus the boundary is the
  cohomological boundary, rather than an unconstrained exact-sequence arrow.
- Weil equivariance: every arrow above, including `boundary`, is a morphism
  of `sfCommonStageWeilSheaf`. The forgetful functor retains the underlying
  geometric arrow, so this explicitly includes its Frobenius commuting equation.
- Negative vanishing: `negative F r hF hr` says `IsZero (R^r j_* F)` for
  every lisse F and every integer r < 0. In particular it applies to all
  three input sheaves, without requiring that they occur in a chosen input.
- R^0 j_* = j_*: `degreeZero` gives the isomorphism for each lisse F,
  and `degreeZero_natural` gives its naturality in every map of lisse sheaves.
- j^*j_*F = F: `counit` gives the isomorphism and
  `counit_normalization` requires its hom to be the actual ordinary adjunction
  counit. Naturality therefore follows from the recorded adjunction.
- j^*R^1j_*F = 0: `positiveOnOpen` is `IsZero` of exactly that object.
- Arbitrary open restriction: the conclusion quantifies over c, d, open
  immersions a : d.C -> c.C and b : d.U -> c.U, and their actual
  `IsPullback b.left d.j.left c.j.left a.left` square. This presents every
  open W of C and U_W = U ×_C W, including W empty and W disconnected.
  `DlOpenImageRestriction.ordinary` and `.higher` give the comparison
  isomorphisms and their `_natural` fields give every sheaf-map square.
  `.higher_normalization` identifies the geometric arrow with the H^r
  image of the actual derived adjunction mate, using the canonical pullback/
  cohomology comparison. `.pullSquare_normalization` uses the existing
  normalized pullback composition maps. `.ordinary_normalization` is the
  ordinary mate of that square, not a selected isomorphism of endpoints.
  `.degreeZero` makes the R^0 identification commute with restriction;
  `.counit` is its open-counit compatibility. `.lisse` retains the restricted
  lisse condition. `.boundary` gives the entire connecting square for every
  morphism from the pulled-back sequence to a short exact lisse sequence;
  it includes the restricted sequence and all its isomorphic presentations.
  The first two sequence arrows commute by the naturality of `.ordinary`.
  Vanishing identifications involve zero objects, whose maps are unique.
  These canonical mates also give the stated compatibility for successive
  opens; no arbitrary comparison or lift is assumed.
- No purity hypothesis: none of the input structures, predicates or theorem
  binders contains weights, an embedding into C, purity, irreducibility or
  semisimplicity. In particular the connecting morphism is not set to zero.

Dependency declarations used (the recorded declarations and their full interfaces
were read, rather than inferred from their names):

- `Sheaf.Paper.CommonStageCurveWeilMiddleExtension`:
  `qbarCurveWeilOrdinaryPushforward`, `qbarCurveWeilPull_isLeftAdjoint`;
  it retains `Scheme.MiddleExtensionCurve` from `CurveMiddleExtension`.
- `Sheaf.Paper.SfWeilSheafComplex`: `sfCommonStageWeilComplex`,
  `sfCommonStageWeilSheaf`, `sfCommonStageWeilForget`, `sfWeilPrimeInvertible`.
- `Sheaf.Paper.SfConstructibleHeart`: `sfCommonStageHeartProperty` and
  `sfCommonStageStandardTStructure` (via the recorded above public imports).
- `Sheaf.Paper.WeilIndSheafCategory`: `zlPull`, `zlWeilPull`,
  `zlPullComp`, `zlFiberMap`, `zlFrobeniusSquare`. The item's stmt_deps gains
  this already-landed owning node `def-zl-weil-ind-sheaf-category`; the
  auxiliary ind-category is not substituted for the constructible inputs.
- `Sheaf.Paper.CommonStageLocallyFree`: `IsCommonStageLisse`, owned by
  the already-landed `def-real-common-stage-lisse`, also added to stmt_deps.
  This is the existing intrinsic common-stage realization of lisse sheaves;
  `LisseIntegralSmallCoefficients` retains the recorded integral-system API.
- `Mathlib.Algebra.Homology.ExactSequence`: `ComposableArrows.Exact`,
  `ShortComplex.ShortExact`, `ComposableArrows.mk₄`.
- Mathlib scheme predicates `Smooth`, `IsOpenImmersion`, `IsSeparated`,
  `LocallyOfFiniteType`, `QuasiCompact` are retained through the curve bundle.
  The direct and cohomology dependency modules below reexport their previous
  declarations and add their missing intrinsic-category interfaces.

Proof-only imports follow the node's eight-step proof, including the abstract
heart triangle/homology interface, completed coefficient pushforward comparison,
right-derived triangulation, constructibility, integral triangle inheritance,
rational transport, scalar extension, integral stratified-perfect identification,
common-stage descent, existing Weil operations, condensed realization,
open direct-image coherence and exact slice restriction. The two proof nodes
`lem-dl-a1-constructible-fibres-exact` and
`lem-a1-qbar-open-closed-cohomology` have no recorded modules on this snapshot;
no nonexistent import is added for them. They remain proof dependencies and
nothing in the theorem assumes their conclusions as extra hypotheses.

Edge cases checked before finalizing the statement: j=id gives a zero boundary
and R^1=0; the zero input and rank zero are allowed; empty C and its necessarily
empty dense U satisfy the vacuous curve conditions; empty W is allowed even for
nonempty C; disconnected curves and opens meeting only some components are
included; negative integer degrees and degree zero are separately quantified;
Qlbar and scheme universes are independent; there is no requirement for a
Frobenius-stable integral lattice. An empty U in a nonempty C fails precisely
the required density condition. A nonzero boundary is permitted, as required
before the parent weight argument kills it.

Searches: the retained searches.jsonl records the earlier LeanFinder query
“For a short exact sequence of lisse adic Weil sheaves, the low degree direct
image sequence is natural and Frobenius equivariant” (eight unrelated generic
exactness/sheaf-map hits), Loogle
`CategoryTheory.ShortComplex.ShortExact, CategoryTheory.Functor.rightDerived`
(no hits), Mathlib grep `WeilSheaf|higherDirectImage|rightDerived.*ShortExact`
in Algebra (no hits), and a LeanSearch query for the natural low-degree
sequence with boundary and open restriction (eight generic module restriction
and Mayer--Vietoris hits). I repeated the Loogle and Mathlib grep queries and
ran LeanFinder “Natural low-degree open direct image exact sequence of lisse
adic Weil sheaves with Frobenius equivariant boundary and compatibility with
open restriction”: eight generic Nobeling, Mayer--Vietoris, completion and
cotangent exactness/restriction results, no matching theorem. Direct rg of
WeilConjectures and lean/Sheaf for the item id and `sfModelDerivedPush` /
`sfModelCohomology` found no pre-existing declaration of the delivered theorem
or helper interfaces. The original affine-line conventions have the legacy
Weil-sheaf predicates, not this fixed-pair common-stage statement. No new DAG
notion is introduced; the two additional dependencies already exist.

There is no statement correction and no STATEMENT-DISPUTED flag. The item is
not its blueprint unit's own statement. All postponed theorems have source and
step-by-step proof docstrings and are listed under their owning nodes.

## Dependency modules

`def-weil-derived-cohomology-sheaves`: the saved lean-only repair points to
`Sheaf.Paper.SfCommonStageWeilCohomology`. The previous
`pbcQbarCohomology` acts on `pbcQbarCategory`, not the intrinsic
`generalAlgebraicallyClosedConstructibleCategory` underlying the recorded Weil
pairs. The module publicly imports that previous interface unchanged. It
uses `constructibleTruncationCohomology` on the already specified standard
t-structure for the intrinsic category. `sfModelPullCohomology` and
`sfModelFrobeniusCohomology` use the existing normalized truncation-unit,
truncation-counit and cohomology formula in `ConstructiblePullbackComparison`.
`sfModelWeilCohomologyPair` applies `IsoAlgebra.mapOfNatIso` to that
comparison. The named membership theorem lets it restrict to the recorded
Weil heart. `sfTruncationShift_existsUnique` specifies its shift maps by
truncation unit/counit equations, and `sfCohomologyShift` takes those uniquely
specified maps. All data definitions are actual constructions; the two
postponed theorems concern these standard cohomology properties. The geometric
base-change instances are actual pullback-projection instances. No coefficient
or scheme universe is collapsed. All helpers are listed in lean.declarations
with this owning node's source/blueprint docstrings.

`def-weil-derived-direct-image`: the saved lean-only repair points to
`Sheaf.Paper.SfCommonStageDirectImage`. The previous `SfIntegralDirectImage`
is an integral finite-reduction tower with its completed derived-limit
presentation; it does not give a functor on the intrinsic common-stage
category, or its action on Weil fixed pairs. The module publicly imports and
retains it. `sfModelDerivedPush` is the right adjoint of the actual geometric
`zlPull`; `sfModelDerivedAdjunction` retains the specifying adjunction.
Its existence theorem's proof explains the identification with the recorded
completed tower through the coefficient pushforward comparison, constructible
restriction, rationalization and descent. Right adjoints with their adjunctions
are uniquely specified up to the canonical compatible isomorphism; no arbitrary
object, unconstrained map or merely inhabited functor is chosen.
`sfModelPullSquare` uses the normalized existing pullback-composition maps.
`sfModelDerivedExchange` is its explicit adjunction mate.
`sfModelPushCommShift` is transported through that adjunction and
`sfModelPushConnecting` applies precisely its shift comparison.
`sfModelWeilDerivedPush` uses the induced inverse-image functor of fixed
pairs. Its forgetful isomorphism is uniquely specified by the equality with
the geometric counit in `sfModelWeilDerivedPush_forget`, and the definition
chooses only that specified isomorphism. Thus all image carriers and arrows
remain the actual geometric ones; no triangulation of fixed pairs is claimed.
The three postponed helper theorems and all concrete data are registered in
the dependency's lean.declarations with source and natural-language proofs.

`lem-weil-pbc-condensed-e-realization`: a further lean-only dependency repair,
using the retained saved module. The required dry run showed that the published
module passes an obsolete explicit k argument to boundedConstructibleUpperStar
and its composition comparison, preventing Along, Data and Exchange from
elaborating. This saved repair uses the current implicit-field API and bundles
Base.model and Base.map to retain the exact geometric morphisms. The existing
lower-star constructor also specializes coefficients to a fixed finite-field
presentation. fieldUpperStar_isLeftAdjoint supplies the same constructible
continuous-E inverse-image adjunction for arbitrary finite E in the scheme
universe, by coefficient transport; fieldLowerStar and fieldAdjunction take
the uniquely specified right adjoint and its adjunction. All coefficient,
scalar-extension, finite-reduction and exchange normalizations are retained.
The owning node is already a proof dependency of the item, so this lean-only
repair is registered through that closure. Its statement, proof and other fields
are unchanged.
The helper theorem carries a source and complete natural-language proof.

## Validation

The required initial dry run failed only at the missing report before any
compile. The completed packet is checked through scompile.py for every
registered module separately, in dependency order, followed by deliver2.py
--no-push and normal delivery. Compiler warnings of the form “declaration
uses sorry” are expected at this stage; other diagnostics are repaired.
The first explicit compilation checked both intrinsic dependency modules and
found the restriction record's nested-carrier comparison exceeded the default
heartbeat count. A scoped allowance with an explanatory comment preserves the
same 60-second wall limit. The dry run additionally exposed the obsolete
coefficient-realization API, which is repaired in the registered fourth module.
Further diagnostics led to inferring the right adjoint directly from the actual
pullback functor, rather than unfolding the internal-module construction to
match a redundant return annotation. Internal point pullback stays reducible
where its section normalization is elaborated and is protected against needless
unfolding in the later coefficient-comparison section. No mathematical clause
or normalization was removed. The repaired coefficient-realization module passed
both wrapper checks without non-sorry warnings (48.9 and 48.3 seconds, within
the unchanged 60-second limit); the temporary type-inspection commands have
been removed before the final packet check.

## Second reading by N5

No second reading by a worker: the dispatcher brief forbids starting other
agents and directs this worker to deliver itself. The maintainer's independent
review is the independent reading. The clause audit above is this worker's
own self-check and is not represented as another worker's review.

The main restriction statement passed the diagnostic wrapper checks in 30.5 and
24.6 seconds after making the two homEquiv objects explicit and removing broad
backward-definitional-equality unfolding options. Structure size and injectivity
generation are disabled for these comparison records. The coefficient dependency
likewise passes explicit bundled endpoints to the current pullback API and explicit
source/target categories to its adjoint constructors. All these changes preserve
the displayed functors and normalization equations. Final recorded signatures
were reread verbatim, all variables and universes are bound, all delivered lines
fit 100 characters, and no diagnostic commands remain in delivered sources.

The full four-module dry-run compilation passed. Preflight then rejected the
standalone line comment immediately following fieldUpperStar_isLeftAdjoint's
sorry body; its lightweight declaration parser included that comment in the
proof. Removing the comment makes the proof literally sorry for that parser.
The coefficient-realization node remains a proof dependency and is not needed
as an additional statement dependency. The two added statement dependencies
are the existing definition nodes for lisse carriers and Weil ind-sheaves.
