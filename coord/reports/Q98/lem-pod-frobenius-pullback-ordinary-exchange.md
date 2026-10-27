## Worker report

The module `Sheaf.Paper.FrobeniusPullbackOrdinaryExchange` states the normalized
pullback-square and ordinary-exchange assertion. Its sole postponed theorem is
`WeilConjectures.OrdinaryAutomorphismSquare.frobeniusPullbackOrdinaryExchange`.
All other declarations are explicit constructions or clause records for this same
assertion, with source and blueprint docstrings. No new independent notion or DAG
node is needed, and no statement correction is made.

The source was read in `literature/blueprint/latest/`: the first sentence of
`sec-poincare-duality/sk-thm-frobenius/prop-weil-operations.proof.md` and the first
paragraph of `sec-six-functors/sk-rem-sf-pf-done/lem-fix-weil-operations.proof.md`.
They use the underlying pullback composition square and ordinary exchange for an
automorphism square. The node's six proof steps specify the coefficient
normalizations implicit there; the theorem docstring carries all six steps.

Hypothesis and clause correspondence:

* The finite-field datum is `D : FiniteFieldDatum.{u}`: its fields give p prime,
  a positive, q=p^a, the field with q elements and its algebraic closure k.
  `l`, `[Fact l.Prime]`, and `_hl : l ≠ D.p` give the other prime and inequality.
  `Ω`, `[Algebra ℚ_[l] Ω]`, and `[IsAlgClosure ℚ_[l] Ω]` give the coefficient
  closure. Each `E : Type u`, `[Field E]`, `[Algebra ℚ_[l] E]`, and
  `[FiniteDimensional ℚ_[l] E]` is an arbitrary finite coefficient extension.
  Small coefficient models `Coefficient.{u} l Ω E` represent actual finite
  subextensions of Ω without identifying Ω's universe with the scheme universe.
* X and Y are `Scheme.{u}` with their `Over (Spec (.of D.k))` structures and
  `LocallyOfFiniteType`/`QuasiCompact` structure morphisms. The morphism f has
  `f.IsOver`, `IsSeparated`, `LocallyOfFiniteType`, and `QuasiCompact` instances.
  These are exactly finite type and separated finite type. The scheme
  morphism-properties dependency is a convention node and has no module.
* The horizontal maps are arbitrary scheme endomorphisms `gX`, `gY` with
  `[IsIso gX]`, `[IsIso gY]`; `w : gX ≫ f = f ≫ gY` is the commutative square.
  Neither horizontal map has an `IsOver` binder. No separatedness of X or Y
  over k is assumed. The existential `iX,iY` discharge invertibility of l
  needed by the existing operations; they are conclusions, not extra hypotheses.
* `integralSquare` is literally `(C gX f).symm`, transport along `w`, then
  `C f gY`, thus c(f,gY) c(gX,f) inverse in the node's order. `Stage.compositor`
  has the existing `IntegralPullbackCompositionFamily` type. The two
  `composition_left`/`composition_right` equations identify its used components
  with `integralComparisonComposition` from the whole-system realization used
  by `pullbackIdentities_scalarExtension`. Thus C is constrained before
  discussing finite reductions; the square is not selected by independently
  evaluated reductions. S retains actual normalized representative data from
  the existing realization API, not an arbitrary map between endpoints.
* `Stage.reduction` states the square reduction equation for every exponent n+1
  and every good representative of K, f-star K and gY-star K. Both target and
  source comparisons are explicitly the iterated `integralPullbackReductionIso`
  maps. `finiteSquare` uses the existing `integralFiniteCanonicalPullbackComposition`
  maps and the same equality w. In Lean's left-to-right order this is
  reduction(a) followed by rho for (f,gY) = rho for (gX,f) followed by finite(a).
* `Stage.rational` is a natural isomorphism of the actual
  `rationalDerivedPullback` composites. `rational_formula` specifies its
  component as localization of the integralSquare component. Naturality is
  therefore quantified over the entire raw tensor Hom group, including every
  sum of pure tensors; it is not restricted to arrows of the form 1 tensor u.
  HEq accommodates the existing theorem-chosen functors' nondefinitional
  object formulas; it asserts equality of those arrows and their endpoints.
* `scalarComposite h k K` is alpha for h at k-star K followed by h-star of alpha
  for k at K. Consequently `(h,k)=(gX,f)` is A, and `(h,k)=(f,gY)` is B.
  `ScalarLaw` says `T(a_E) ≫ B = A ≫ a_L`, both integrally and rationally.
  Every `ι : E →ₐ[ℚ_[l]] L` is included, including identity embeddings and
  composite embeddings. The completed scalar functor is the existing
  constructible restriction of `integralScalarExtensionOfUniverses`, using
  its established auxiliary p=0 convention, not a different construction.
* `Common.comparison` is the natural isomorphism on the actual common-stage
  categories and `Common.component` says its component at (E,K) is precisely
  the image of `(SE E).rational` under the existing stage inclusion. This is
  the actual quotient class. `Common.left_arrows` and `right_arrows` give
  the prescribed A/B-conjugation formulas for every larger common stage L and
  every arrow represented at L. `commonCompositeComparison` is the composite
  of the two published pullback scalar comparisons with their actual
  transition identifications. Using the quotient arrow `ofHom` on the left
  ensures equivalent representatives and all further towers give the same
  output, not merely arrows from a fixed preferred stage. Naturality of
  `Common.comparison` covers those same quotient arrows. The specified scalar
  comparisons already carry the identity and tower identifications of the
  dependency interfaces; none are replaced by strict identity choices.
* `Stage.transportX`, `.transportY` and the corresponding fields of `Common`
  state exact equivalences with inverse functors literally pullback along
  `inv gX`, `inv gY`. `ExactInverse` records CommShift, IsTriangulated and both
  inverse-composition isomorphisms on those actual functors, as the item
  asserts. No new inverse functor is chosen.
* `ExchangeOnDomains` retains every supplied full domain and its actual
  restricted functors. Its hF,hG,hH and inverse-preservation witnesses express
  the source's stipulated closure under the displayed operations. The inverse
  closure is needed to restrict horizontal equivalences, not a new geometric
  assumption. `onDomain` is only Mathlib's full-subcategory lift of the original
  functor; `onDomainSquare` restricts the same square componentwise. `R,adj`
  are the supplied ordinary direct image and ordinary adjunction. The assertion
  is uniform in this supplied ordinary adjunction, so it applies in particular
  to the specified normalization without choosing an alternative direct image.
  It asserts invertibility of the mate of the inverse square, and its component
  is exactly `eta ≫ R.map(a inverse) ≫ R.map(P_X.map(epsilon))`.
  This is the direct-image definition in `ExchangeProjectionStage.exchange`,
  using the identical `mateEquiv` constructor, specialized to equal vertical
  operations. Unrelated compactification and tensor data of that larger record
  are not required merely to express its ordinary-exchange clause.
* No input has a Weil structure, and no Karoubi completion, rational-to-finite
  functor, arbitrary inverse functor, or reduction-faithfulness premise occurs.

Dependency declarations read and used:

* `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum` and its
  field instances, via the public import of IsomorphismFieldTransport.
* `Sheaf.Paper.DerivedPullbackTensorHom`: `constructibleIntegralPullback`,
  `rationalDerivedPullback`, `integralPullbackScalarComparison`,
  `rationalPullbackScalarComparison`, `commonStageDerivedPullback`,
  `commonStagePullbackObject`, `commonStagePullbackComparison`.
* `Sheaf.Paper.IntegralPullbackComposition`: `IntegralPullbackCompositionFamily`,
  `integralPullbackComposition`, `integralPullbackReductionIso`.
* `Sheaf.Paper.IntegralFinitePullbackComposition`:
  `integralTowerGeneralPullbackComposition`, `integralFiniteCanonicalPullbackComposition`.
* `Sheaf.Paper.IntegralOperationsScalarComparisons`:
  `scalarPullbackCompleted`, `scalarOperationsOrdinary_tower` and its unit law.
* `Sheaf.Paper.PullbackIdentitiesScalarExtension`:
  `pullbackIdentities_scalarExtension`; its public realization API supplies
  `IntegralComparisonSystem` and `integralComparisonComposition`.
* `Sheaf.Paper.IntegralScalarExtensionUniverses`:
  `integralScalarExtensionOfUniverses`; constructible scalar restriction and
  the rational scalar functor are the existing dependency constructions.
* `Sheaf.Paper.SfDerivedDirectImage`: `SfIntegralDirectImage`, its Roos data,
  and finite-reduction comparison were read. R remains the supplied ordinary
  functor on its stipulated domain; there is no second integral construction.
* `Sheaf.Paper.SfRationalizationKaroubi`: `sfRationalConstructibleCategory`,
  `sfRationalConstructibleLocalization`, `sfRationalScalarExtension`.
* `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients`: the existing common-stage
  category, `inclusion`, `ofHom`, and coefficient transition comparisons.
* `Sheaf.Paper.ExchangeProjectionSuppliedDomains`:
  `ExchangeProjectionStage.exchange`, with its actual mate formula.
* `WeilConjectures.SixFunctors.Etale.Derived.Adjunctions`:
  `AlgebraicGeometry.Etale.mapDerivedUpperStarLowerStarAdjunction_comp_eq`
  and the ordinary-adjunction docstrings. This recorded interface specializes
  to etale coefficients; the item supplies its higher-coefficient ordinary
  adjunctions explicitly, so it requires no replacement interface for that datum.
* `Sheaf.Paper.IsomorphismFieldTransport`: `isomorphismFieldTransport` and its
  complete Stage/Common records were read. It supplies the exact horizontal
  equivalences used in the proof plan; only the exactness/inverse clauses this
  item asserts are retained, rather than adding its other coefficient claims.
* `Sheaf.CategoryTheory.MateIsoAlongEquivalences`:
  `CategoryTheory.isIso_mateEquiv_of_isEquivalence_of_fullyFaithful` (proof import).

Edge cases checked before and after writing: identity gX,gY (equality transports
remain explicit); f identity; empty schemes; zero complexes; exponent n=0 means
level 1, so no positive finite level is lost; E=L with identity inclusion; a
ramified coefficient inclusion; arbitrary common-stage representatives and an
arbitrary further field; nonseparated X,Y; semilinear horizontal maps not over k;
and independently sized Ω. The raw categories and their actual small coefficient
models impose no new cardinality or site-universe equality. There are no index
nonemptiness assumptions excluding an empty case.

Searches (all through prescribed msearch.py where applicable):

* LeanFinder query `commuting scheme automorphisms derived pullback natural
  isomorphism ordinary direct image exchange mate`: 8 hits, ordinary O_X-module
  pullback composition/adjunction facts, no normalized coefficient-stage assertion.
* Loogle query `CategoryTheory.Adjunction, conjugateEquiv, NatIso`: 0 hits;
  service reported unknown identifier conjugateEquiv.
* Mathlib grep query `frobenius.*exchange|automorphism.*pullback`: 0 hits.
* LeanSearch query `Derived pullback commutes with scheme automorphism ordinary
  direct image exchange`: 8 hits, ordinary scheme-module pullback/adjunction facts.
* rg across project `Sheaf` and `WeilConjectures` for Frobenius exchange,
  automorphism squares, ordinaryExchange, and the proposed declaration names.
  `Etale/Derived/WeilOperations.lean` has `isIso_derivedBaseChangeMap_of_isIso`,
  but it concerns etale finite coefficient operations and does not state this
  node's completed integral normalization, scalar square, raw rationalization
  or common-stage representative clauses. Existing Frobenius compact-support
  modules concern Ex_!, not this Ex_* assertion.
* The exact node id search in `lean/WeilConjectures` produced no declaration;
  the upstream name index has no match for this whole normalized statement.

No dependency node record is changed. No STATEMENT-DISPUTED issue was found.
All writes are confined to the assigned sandbox; all compilation uses scompile.py.

Validation: the final module passed scompile.py in both sandbox and final library
module modes without errors or non-sorry warnings. The source has one whole-proof
sorry, the theorem signature matches lean.statement verbatim, all 15 declarations
are listed, and every line is within 100 characters. The node copy differs from
its read-only base only in lean. The delivery wrapper supplies the independent-review
placeholder; this report makes no claim of a second reader.

## Second reading by Q98

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
