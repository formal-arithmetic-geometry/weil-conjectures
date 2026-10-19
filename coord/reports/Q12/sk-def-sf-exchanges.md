## Worker report

The delivery is `Sheaf.Paper.SfExchanges`. Its declarations collect the typed
exchange and projection constructions of blueprint main-20261015, unit
sk-def-sf-exchanges, order 1701. The source unit and its defining
unit/comparison/counit sentence were read in full. The statement is unchanged.
There is no assertion of invertibility or compactification independence.

Clause-by-clause reading:

* The schemes and arrows are `X', X, Y', Y`, `f, f', g, g'`, with exactly the
  displayed directions. `sfExchangeStarPlus` takes only `CommSq g' f' f g`:
  Cartesianity is unnecessary for this arrow. Its source is
  `(proEtaleConstantModuleDirectImage f A).rightDerivedFunctorPlus` followed
  by `(sfIntrinsicPullback A g).mapDerivedCategoryPlus`; its target is
  pullback by g' followed by the bounded-below direct image of f'. Thus its
  categories are the actual D+ categories of intrinsic pro-etale modules,
  not unbounded categories with an unrecorded boundedness assumption.
* The defining composite for Ex_* is `mateEquiv` for the two actual
  `sfIntrinsicConstantModuleAdjunction` adjunctions, derived by `.derivedPlus`.
  The intervening comparison is the inverse of `sfIntrinsicSquarePullback`,
  descended by `mapDerivedCategoryPlusNatIso` with the derived composition
  isomorphisms inserted. This is exactly the f' unit, pullback comparison,
  f counit in that order. No independently chosen exchange arrow is supplied.
* For Ex_!, `sfExchangeShriek` uses the compactifications `c, c'`, their
  projection `gbar`, and the proper and open Cartesian squares. This retains
  the compactification choice of sk-def-sf-operations (iv). Its endpoints
  are `sfIntrinsicCompactSupport c A` then pullback by g, and pullback by g'
  then `sfIntrinsicCompactSupport c' A`. The formula is
  `compactificationExchangeFromData`, with the actual intrinsic proper
  adjunctions, canonical pullback composition, and normalized open exchange.
  The open exchange is taken from `proEtale_openSquareExchange`; its
  `canonical` field fixes the inverse to the specified open-adjunction mate.
  Consequently the proof choice does not choose an arbitrary isomorphism.
  These maps exist on all ambient unbounded finite-coefficient complexes.
* The separated finite-type hypothesis on f supplies compactifications in
  the source setting; a chosen compactification is retained explicitly as
  the operational definition requires. The formulas themselves need no
  additional finite-field, smoothness, properness, or separatedness of g.
  The direct-image formula is even defined for every commutative square.
* Finite coefficients are exactly `Padic.coefficientExtensionRing l E n`,
  with `[Fact l.Prime]`, finite `E / Padic l`, and `hn : 1 ≤ n`. In particular
  exponent one is retained. `sfExchangeStarPlus` is stated for arbitrary
  finite coefficient rings and specializes to every one of these quotients.
  All module realizations use the published ULift equivalence, so coefficient
  and small-site object universes are not forced equal.
* The adic parenthesis is `sfExchangeShriekCompleted`: a transparent use of
  `completedCompactSupportExchange`, with its actual `AdicCoefficientDatum`,
  ideal, generating tuple, `cbcCompleteProperty`, and chosen base change.
  Its endpoints use `d.completedPull g` and `d.completedPull g'`. This is
  not the ordinary pullback mate with a different name. The generating tuple
  can be empty. No arbitrary lift from the finite reductions is chosen.
* For the projection, K belongs to
  `(intrinsicFiniteTorsionConstructible l E n hn X).FullSubcategory`, precisely
  Db_c. L belongs to
  `(finiteTorConstructible l E n hn Y).FullSubcategory`, precisely Dctf.
  In particular there is no finite-Tor assumption on K. The ambient arrow
  `sfFiniteProjectionAmbient` packages the two-variable component of the existing
  `finiteRingCompactSupportProjection`: the proper counit projection followed
  by the open projection and pullback-composition identification, in the
  canonical intrinsic realization. Its source and target are respectively
  Rf!K tensor L and Rf!(K tensor Lf*L), not chosen substitute objects.
* `sfFiniteProjection_boundedBelow` states just the two endpoint typing
  facts implicit in the source's phrase “in D+(Y,Lambda)”. Its named proof
  is `sorry`, with a complete natural-language proof in the docstring.
  `sfFiniteProjectionPlus` is `ObjectProperty.homMk` applied to the existing
  ambient arrow's `hom`, using those proofs; it therefore changes no morphism data.
  The original projection is a natural transformation of curried bifunctors,
  and full-subcategory restriction preserves naturality in both K and L.
* At the other coefficient stages the dependency def-exchange-projection
  explicitly defines the maps relative to supplied operation/adjunction/
  comparison data on closed full domains. `sfExchangeProjection d` packages
  exactly its three natural transformations, `d.exchange`,
  `d.compactExchange`, and `d.projection`, with all three endpoint types
  written out. In an integral instance the pullback and tensor in d are
  completed ones; rationalization and common-finite-field representatives
  are taken using the dependency's supplied coefficient comparisons and
  identity/composition normalizations. This construction does not assert
  the existence of an ambient exceptional adjoint or extend operation domains.
  The completed ambient component is separately attached above, rather than
  identifying ordinary and completed pullbacks. The operation catalogue
  sk-def-sf-operations has no aggregate Lean record, but no new operation
  notion from that catalogue is needed: each operation used here already has
  its own published declaration through the more specific dependencies.

Dependency declarations read and used:

* `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses`,
  `SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses`,
  and Mathlib
  `CategoryTheory.IsGrothendieckAbelian.enoughInjectives`. The local instance
  `sfExchangeEnoughInjectives` activates this published property at site object
  universe u+1, morphism universe u, and module universe u+1. No Abelian or
  derived-category instance is replaced or chosen.

* Mathlib `CategoryTheory.Adjunction.Mates`, `CategoryTheory.mateEquiv`.
* `Sheaf.AlgebraicGeometry.SfIntrinsicRealizationTransport`,
  `AlgebraicGeometry.Scheme.sfIntrinsicConstantModuleAdjunction`.
* `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction`,
  `CategoryTheory.Adjunction.derivedPlus`.
* `Sheaf.AlgebraicGeometry.ProEtaleOpenSquareExchange`,
  `sfIntrinsicSquarePullback`, `sfIntrinsicDerivedSquarePullback`,
  `sfIntrinsicDerivedOpen`, `proEtale_openSquareExchange`, and
  `SfOpenSquareExchangeData.canonical` in `AlgebraicGeometry.Scheme`.
* `Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport`,
  `AlgebraicGeometry.Scheme.sfIntrinsicCompactSupport`.
* `Sheaf.Paper.ExchangeProjectionSuppliedDomains`,
  `CategoryTheory.SuppliedExchangeProjection.compactificationExchangeFromData`
  and `ExchangeProjectionStage.exchange`, `.compactExchange`, `.projection`.
* `Sheaf.Paper.FiniteRingCompactSupportProjectionMap`,
  `AlgebraicGeometry.Scheme.finiteRingCompactSupportProjection`.
* `Sheaf.Paper.IntrinsicFiniteTorsionConstructibility`,
  `AlgebraicGeometry.Scheme.intrinsicFiniteTorsionConstructible`.
* `Sheaf.Paper.FiniteTorAmplitude`, `WeilConjectures.finiteTorConstructible`.
* `Sheaf.Paper.CompletedCompactSupportExchange`,
  `AlgebraicGeometry.Scheme.completedCompactSupportExchange`.
* The recorded `Sheaf.Paper.PbcActualRingedExchange` and its ordinary/complete
  pull-square comparisons were read: they fix the same mate, but the ordinary
  record is unbounded and its chosen-square interface does not express the
  unit's weaker commutative-square D+ clause. The derived-Plus construction
  above uses the actual ordinary adjunctions instead.
* The recorded finite etale compactification exchange
  `AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactificationPlusBaseChangeMap`
  was read in the upstream source. It is the etale presentation of the
  compactification construction; the intrinsic pro-etale map above directly
  uses the proper and open factors of def-exchange-projection.

Edge cases checked against the formulas: arbitrary commutative non-Cartesian
squares for Ex_*; identity arrows and identity squares (the mate reduces by
triangle identities); proper f with identity open factor; open f with identity
proper factor; zero complexes and empty schemes; quotient exponent one; arbitrary
positive exponents; empty ideal-generating tuple in completed exchange. K is
allowed to have infinite Tor dimension. No claim that any of these arrows is
invertible is included. The additional cited construction node has no dependency path to
sk-def-sf-exchanges, so its addition introduces no cycle.

Searches actually run for an existing complete attachment:

* msearch leanfinder, “exchange and projection natural transformations for
  derived pullback direct image compact support sheaves”: eight generic
  underived sheaf pullback/pushforward and tensor-pullback results, including
  `TopCat.Sheaf.pullbackPushforwardAdjunction` and
  `SheafOfModules.conjugateEquiv_pullbackComp_inv`; no complete typed attachment.
* msearch loogle, “CategoryTheory.mateEquiv, derivedBaseChangeMapPlus,
  projectionMapOfCompactification”: no hit; unknown derivedBaseChangeMapPlus
  in Mathlib. The upstream declarations were then read directly.
* msearch grep, `derivedBaseChangeMapPlus|projectionMapOfCompactification|ExchangeProjectionStage`
  over all Mathlib: no hits.
* msearch leansearch, “derived sheaf exchange natural transformation projection
  formula compact support”: eight generic sheaf/derived-natural-transformation
  results, including `Functor.rightDerivedNatTrans` and
  `SheafOfModules.pushforwardNatTrans_app_val_app`; no full match.
* `rg` in WeilConjectures for derivedBaseChangeMapPlus, compactification base
  change, and projectionMap found the etale and finite pro-etale constructors.
  `rg sk-def-sf-exchanges` found no declaration attaching the complete unit.
* `rg` in shared lean/Sheaf found ExchangeProjectionSuppliedDomains,
  CompletedCompactSupportExchange, ProEtaleOpenSquareExchange, and the
  maintainer's new standalone FiniteRingCompactSupportProjectionMap. Their
  full signatures and defining data were read. They are reused above.
* The source unit was read under literature/blueprint/main-20261015, not the
  old master snapshot. No statement fault or disputed claim was found.

No new definition node or dependency-module repair is needed. The existing
landed definition node added to stmt_deps is
def-sp-finite-ring-compact-support-projection-map, owning the finite projection
constructor. The normalized open exchange is already a notion of
def-exchange-projection: the trace lemma supplies its unique inverse-mate
realization, and is used for this proof, not as a new statement parameter.

Validation: the final scompile.py run compiled the isolated sandbox module
(16.3 seconds) and final library-path module (6.3 seconds), with no errors or
warnings. The initial timeout was repaired by assigning the finite projection
a compact `Arrow` result type instead of re-inferring and expanding its entire
bifunctor type. The D+ construction uses the existing enough-injectives result
activated at the correct independent site universes. The first delivery
preflight found that its declaration scanner did not recognize `local instance`;
this is now a named instance with registration scoped locally. It also suggested
avoiding a theorem in stmt_deps: the open-exchange existence theorem is used only
to construct the already-defined canonical comparison, so that redundant
statement dependency was removed.

The repaired deliver2.py --no-push run printed OK: preflight and all per-file
compiles passed (dry-run commit dd7d4d2906).

## Second reading by Q12

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
