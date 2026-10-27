## Worker report

The module `Sheaf.Paper.SfFieldMateDomain` states
`WeilConjectures.sf_fieldMateDomain`, with the single postponed proof `by sorry`.
`SfFieldMateDomain` is a Prop structure grouping the clauses of this node, not a
new coefficient category or a choice of operation functors. Three public instances
cache existing category/preadditive instances at their already prescribed Hom
universe; each is `inferInstance` and adds no mathematical assumption.

Hypothesis and clause correspondence:

- `D : FiniteFieldDatum` records p, a, q, k0 and its chosen algebraic closure k.
  `C : D.CoefficientDatum` records the prime ell, ell != p, and the chosen Qbar.
  `E`, `Field E`, `Algebra (Padic C.l) E`, and `FiniteDimensional` record the
  finite extension. Its valuation ring and uniformizer are the dependency's
  `pbcIntegralRing`, `pbcIntegralDatum`, and `pbcUniformizer`, not arbitrary rings.
  `n`, `hn : 1 <= n`, and `_operations : SixFunctorOperationDatum D C E n hn`
  retain the specified finite-coefficient and six-functor datum.
- Each of `X Y X' Y' : SixFunctorSpace D` is an object of the finite-type
  subcategory of schemes over Spec k. Its property supplies locally finite type
  and quasi-compactness of its structure map; the four `IsSeparated` structure-map
  instances impose separatedness. The four morphisms in that category are
  k-morphisms, with explicit separated, locally finite-type and quasi-compact
  instances for each. `sq` is precisely `ChosenCartesianSquare` on their underlying
  maps, retaining its chosen pullback identification and both projection equations.
- `SfFieldMateDomain` supplies Noetherian instances, the four finite-dimensionality
  Facts and invertibility Facts as CONCLUSIONS. None is added as a hypothesis of
  `sf_fieldMateDomain`. `invGlobal` is the global coefficient-prime invertibility
  needed by the existing smooth interface. All follow from the geometry dependency.
- `properRational` assumes only `IsProper f` and quantifies over every raw rational
  constructible input `K`. It asserts the two actual completed endpoints belong to
  the full integral constructible category, and `IsIso` for the rationalization of
  `ObjectProperty.homMk` of `sbcExchangeApp`. This is the raw localized integral
  mate, not an unspecified arrow with the same endpoints.
- `properCommon` supplies a normalized `PbcQbarExchangePresentation`, asserts
  invertibility at every common-stage object and every finite stage, the exact
  `atStage` equation for every overfield (including the identity extension), and
  the naturality equation for every isomorphism of pair representatives. Its
  fields normalize the finite-level operations and exchange, so this retains
  finite-field and representative independence of the specified maps.
- `smoothRational` uses `[Smooth g]` and the qcqs hypotheses on f, already implied
  by the theorem's separated finite-type geometry. The square is transposed by
  the published `exchangeTransposeSquare`, giving exactly (g,f,f',g'). `L` is
  `IntegralLattice`, hence includes the specified lattice isomorphism. The premise
  is exactly `IsFiniteLevelEtaleAdmissible`. The four conclusion clauses are
  ambient `IsIso`, equality of the transported and canonical rational maps,
  equality for every other admissible lattice presentation, and conditional
  `SbcConstructibleExchangeRepresentation` under square admissibility. That last
  predicate includes the single [a,b] for every level and all four output families.
- `smoothCommon` supplies the coefficient theorem's normalized `Presentation`.
  Its first clause assumes an admissible finite-stage representative, a chosen
  representative isomorphism, and existence of admissible lattices after every
  finite overfield, precisely the representative-wise ambient hypotheses of the
  item. It gives invertibility in the ambient complete Qbar category. `alpha_eq`
  identifies the finite-stage maps with the Karoubi extension of the raw rational
  exchange, so the identity-idempotent inclusions retain the actual raw map.
  Its second clause is the `atStage` equality for all common fields, including
  reflexive extensions. Its third clause retains independence of lattice choices.
  Exchange is a natural transformation on the quotient pair category; its
  naturality also identifies isomorphic representatives.
- `smoothCommonConstructible` requires square admissibility at the relevant
  finite stage and asserts the existing finite-stage constructible representation.
  The next clause sends every such finite-stage isomorphism beta to gamma with
  `gamma.hom = stageInclusion.map beta.hom`; its formula with `mkHom` at every
  overfield proves the same class represents it there. This gives the common-stage
  constructible isomorphism for the representing beta without assuming operation
  preservation on all objects. No ambient constructible landing is asserted
  without this finite-stage hypothesis, and there is no reduction of a rational
  object anywhere in the module.

Dependency declarations read and used:

- `Sheaf.Paper.SixFunctorOperationDatum`: `WeilConjectures.SixFunctorOperationDatum`,
  together with its existing `SixFunctorSpace` and finite-field/coefficient datum.
- `Sheaf.AlgebraicGeometry.ChosenCartesianSquare`:
  `AlgebraicGeometry.ChosenCartesianSquare`.
- `Sheaf.Paper.ExchangeProjectionSuppliedDomains`:
  `ExchangeProjectionStage.exchange`, the unit/comparison/counit mate convention;
  `sbcExchangeApp` is the concrete completed instance of that formula.
- `Sheaf.Paper.PbcRationalCategory`: `PbcRationalDerivedCategory`,
  `PbcRationalCategory`, `pbcRationalization`; `PbcRationalConstructible` is the
  published alias on the same actual completed coefficient datum.
- `Sheaf.Paper.PbcQbarCategory`: `pbcQbarCategory`, its scalar action and
  triangulation, repaired as an existing exact binding below.
- `Sheaf.Paper.AdmissibleLattices`: `IntegralLattice`,
  `IsFiniteLevelEtaleAdmissible`, `IsSquareConstructiblyAdmissible`.
- `Sheaf.Paper.ExchangeFunctoriality`: `exchangeTransposeSquare`. This is an existing
  square-label helper, not a new notion or statement dependency. Its module does
  not reach this item (the DAG search found no dependency cycle).
- The proof imports also retain `SfBaseChangeGeometryHypotheses`,
  `SbcCompletedOperations`, `ConstructibleCompleteBaseChange`, `FourArrows`,
  `CompletedBaseChangeMap`, `FiniteExtensionProperBaseChange`,
  `QbarProperBaseChange`, `ECoefficientSmoothBaseChange`,
  `QbarCoefficientSmoothBaseChange`, `AmbientCompleteCoefficientCategories`,
  `PbcScalarExtension`, `PbcDescentFunctors`, and `CommonStageCalculus`.
  The proper and smooth presentation/representation types are used in the
  statement, so their defining modules are public imports.

Edge cases checked before writing: empty schemes and empty fibres remain covered
(the geometric conclusions use natural bounds, with dimension bottom allowed);
zero objects and uniformizer-torsion integral representatives are retained by raw
localization; n=1 corresponds to smooth index m=0; identity base changes and
identity coefficient extensions are not excluded; all overfields and all lattice
presentations are quantified, not just one preferred representative; no arbitrary
ambient Karoubi object is asserted to come from a raw rational object. Sites and
coefficients retain their inherited u+1/u small-site size conventions. Universe u
is arbitrary; the three cached instances select the existing Hom universe u+2.

Searches made using the prescribed msearch.py wrapper:

- leanfinder: “Proper and smooth base change for rational l-adic completed sheaves
  with admissible lattices and common field stages”: eight hits, on BDeRhamPlus,
  condensed modules and adic module completion; no match.
- loogle: `CategoryTheory.IsIso, CategoryTheory.NatTrans`: zero hits.
- grep: `rational.*exchange|adic.*base.?change|etale.*base.?change`: fifteen hits,
  all ordinary algebra/scheme base-change or etale stability, no such coefficient
  domain assertion.
- leansearch: “Proper and smooth base change for rational l-adic sheaves with
  admissible lattices”: eight hits, on stability of smooth/proper morphisms and
  smooth ring algebras under base change, no match.
- rg in `lean/WeilConjectures` and `lean/Sheaf` for the item id: no match.
  rg for `sbcRationalExchange`, rational exchange, and proper exchange finds the
  separate coefficient theorems and the smooth clause of `ExchangeFunctoriality`,
  not the combined proper/smooth assertion and conditional constructible descent.
- Names `SfFieldMateDomain` and the new declaration names were checked against
  the project, upstream name index and Mathlib. No pre-existing declaration.

No statement correction or disputed mathematical statement is needed. All edits
are in the authorized sandbox, with no direct git command in the shared clone.

## Dependency modules

None. An earlier draft rebound the record of `def-weil-pbc-qbar-category` to
`pbcQbarCategory`; that rebind is not part of this delivery. The dependency node is
byte-identical to the live node, and its record (`Sheaf.Paper.IntrinsicQbarCategory`,
`intrinsicPbcQbarCategory` and seven companions) is unchanged. The statement uses the
pair category `pbcQbarCategory` of `Sheaf.Paper.PbcQbarCategory` directly, because the
landed proper and smooth Qbar theorems are stated on it. That category is the pair
category P_T over the raw PBC rational stages, which is the category the node describes.

## Second reading by Q01

This is an independent reading of the delivered module against the node, its
statement dependencies, and the coefficient theorems the node assembles.
It replaces the earlier self-audit and the dispatcher retry log.

Node clauses, the Lean that renders them, and the verdict for each:

1. k, l != p, E/Q_l finite, O_E, varpi, A_n: `D : FiniteFieldDatum`, `C : D.CoefficientDatum`
   (`different : l != D.p`, Qbar), `E : Type u` finite over `Padic C.l`;
   O_E/varpi come from `pbcIntegralDatum`/`pbcUniformizer`. The six-functor datum
   `(n, hn, _operations)` is unused, which is the usual sf pattern for "Use
   [def-fix-six-functor-datum]". OK.
2. Separated finite-type k-schemes and k-morphisms, and the Cartesian square: `X Y X' Y' :
   SixFunctorSpace D` with separated structure maps. The four `Over` morphisms carry
   separated, LocallyOfFiniteType and QuasiCompact instances. Finite type
   follows from the finite-type corners, so these instances add no assumption.
   `sq : ChosenCartesianSquare g' f' f g` on the underlying maps. OK.
3. The geometric consequences (Noetherian, finite dimension, l invertible on stalks
   and globally) are structure fields, so they are conclusions and not hypotheses.
   They are true for finite-type k-schemes with l != p. OK.
4. Proper case, E: `properRational`. For every raw rational object K it gives
   constructible membership of Lg^*Rf_*K and Rf'_*Lg'^*K, plus `IsIso` of the
   rationalization of `homMk (sbcExchangeApp (exchangeTransposeSquare sq) K)`.
   `sbcExchangeApp` is the unit/theta/counit mate
   Rf'_*Lg'^*(eps_f) o Rf'_*(theta) o eta_{f'}, and the transposed square gives exactly
   (f_s,g_s,h_s,e_s)=(g,f,f',g'). This is the isomorphism in D^b_c(Y',E). OK.
5. Proper case, common stage: `properCommon` is `qbar_properBaseChange` verbatim. The
   presentation pins its exchange (`exchange_eq`) to `pbcActualCompletedExchange sq`.
   Its clauses are: invertibility at every common-stage object and at every finite
   stage, `atStage` at every overfield M including the reflexive one, and naturality
   in representative isomorphisms. Together these give field and representative
   independence. OK.
6. Smooth case, E: `smoothRational` is `eCoefficientSmoothBaseChange` verbatim, on
   the transposed square (S_s,X_s,T_s,Y_s)=(Y,Y',X,X'). Its four conjuncts are:
   ambient IsIso, transported = canonical, lattice independence, and
   square-admissible gives `SbcConstructibleExchangeRepresentation` (one interval
   [a,b] for all levels and all four output families). OK.
7. Smooth case, Qbar: `smoothCommon` is `qbarCoefficientSmoothBaseChange` verbatim,
   with Fact instances iX=g, iS=1_Y, iT=f, iY=g'≫f, matching e_s≫g_s.
   - The representative-wise admissibility and overfield stability are premises,
     as the node requires.
   - `alpha_eq` (raw exchange through the identity-idempotent inclusion) is inside
     `Presentation`.
   - It also gives atStage at further fields and finite-E lattice independence.
   No ambient constructible landing is asserted. OK.
8. Conditional constructible landing: `smoothCommonConstructible` has a finite-stage
   square-admissible premise. It gives the finite-stage representation, and states
   that a finite-stage isomorphism beta gives the common-stage isomorphism
   iota_M(beta), represented at every N by T_a beta. The second conjunct holds for
   any beta, so it is elementary. This matches the node, whose content here is
   exactly step 6 (u_M^{-1} stays in the full stage category). No finite reduction
   of a rational object appears anywhere. OK.

Edge cases:
- Empty schemes: the Noetherian, dimension and unit facts all hold.
- Identity extension: covered by atStage with M = stage.
- n = 1: corresponds to smooth index m = 0.
- Zero objects and uniformizer torsion: retained by raw localization.
- Universes: E and Qbar are in `Type u`, the same as the sbc/pbc interfaces;
  no universe equality is imposed beyond these.

Searches: the worker's leansearch, loogle, leanfinder and grep records are above.
I also grepped the live tree for `SfFieldMateDomain`, `sf_fieldMateDomain` and
`sfFieldMateStage`: no clash.

Advisory notes (not faults):
- The statement uses theorem-module packaging, which carries no stmt_dep:
  `PbcQbarExchangePresentation`, `Presentation`, `sbcTransportedExchange`,
  `SbcConstructibleExchangeRepresentation`, `sbcExchangeApp`. These are the
  witness records of the assembled theorems, pinned to the landed canonical maps.
- `pbcQbarCategory` is used directly rather than the recorded
  `intrinsicPbcQbarCategory`.
