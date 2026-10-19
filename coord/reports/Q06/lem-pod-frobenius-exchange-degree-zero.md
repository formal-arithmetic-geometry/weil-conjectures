## Worker report

The module `Sheaf.Paper.FrobeniusExchangeDegreeZero` states
`WeilConjectures.PodDegreeZero.frobenius_exchange_degree_zero`. Its only postponed
proof is this theorem. The auxiliary declarations construct canonical coordinate
identifications and section maps, with real data. No dependency node or natural
statement was changed, and no new independent notion or DAG node was needed.

Hypotheses and objects:

- The section binder `D : FiniteFieldDatum.{u}` retains p, a, q, the arbitrary
  finite field k₀, its chosen algebraic closure k, and their structure map.
- `l : ℕ`, `[Fact l.Prime]`, `hl : l ≠ D.p`, and the field, algebra and
  finite-dimensional instances on `E : Type u` give precisely the prime and
  finite extension E/Q_l. `Padic.coefficientExtensionRing l E (n + 1)` uses the
  dependency's valuation ring and chosen uniformizer. Index `n : ℕ` represents
  every positive exponent, including exponent one when n=0.
- `Y₀ : Over (Spec (.of D.k₀))` has `[LocallyOfFiniteType Y₀.hom]`,
  `[QuasiCompact Y₀.hom]`, `[IsSeparated Y₀.hom]`. These are exactly separated
  finite type over k₀. No properness, connectedness, smoothness, Weil structure,
  chosen section or k-linearity of Frobenius is assumed.
- `D.geometricFiber Y₀`, its `.left` and `.hom` are Y and a:Y→Spec k.
  `FrobeniusExchange.galois D Y₀` is g; `(frobeniusPointIso D).hom` is h.
  Their commuting square is the last clause of `D.frobenius_square_cartesian`.
  `galoisIsIso` merely exposes the instance of the prescribed automorphism.
- `M : integralOperationsFiniteModules l E (D.geometricFiber Y₀).left n`
  is an actual sheaf over the constant ring A_Y on the small pro-etale site.
  `_hM` is exactly `IsConstructibleProEtaleModuleSheaf ... M`, using the
  dependency's finite-ring instance. `DerivedCategory.singleFunctor _ 0` places
  M in degree zero. `_hRa` is exactly `intrinsicFiniteTorsionConstructible` of
  the actual `proEtaleConstantDerivedDirectImage` of this single object at s.
  Thus the point transport is in its stated bounded-constructible domain.
- All categories live in an arbitrary common universe u. The site retains
  object universe u+1 and morphism universe u; module sections have size u+1.
  `pointModuleDerived` reuses `HasDerivedCategory.ofIsGrothendieckAbelian` for
  exactly the point target used by the recorded transport. There is no equation
  imposed between site object and morphism universes.

Canonical maps and identifications:

`tensorUnit` is the degree-zero term of the recorded
`inverseImageFiniteComparisonComplex`, conjugated only by the single-complex
term identifications. `intrinsicUnit` composes the existing unit-preserving
`inverseImageFiniteIntrinsicPullbackComparison`. It is precisely j:x↦x⊗1 in
intrinsic coordinates. The dependency identifies its inverse lambda with
x⊗b↦c_A⁻¹(b)x; the theorem writes the equations using j rather than choosing
another inverse.

`directZero` is the composite of
`homologyRightDerivedFunctorObjSingleFunctorIso M 0` and
`rightDerivedZeroIsoSelf.app M`. Its finite-limit instance comes from the
recorded left-exactness theorem; the existing ringed-site Grothendieck theorem
supplies enough injectives, without an extra assumption. `exchangeZero`
conjugates H⁰ of the actual `FrobeniusExchange.finiteExchange` by this comparison,
exact-pullback homology comparison, and the single/pullback comparison. This is
the intrinsic presentation of the specified mate, as used in the recorded
ordinary transport. No arbitrary exchange or base-change isomorphism is supplied.

`proEtaleBaseChange` orders its factors U×_sY. `squareArrow` is therefore
(v,y)↦(v,g(y)) from U×_sY to (U,h∘u)×_sY. The `pullback.map` uses the actual
commuting square and identity on U. `underivedMate` restricts M along this arrow.
The inverse-image colimit counit formula of Tags 00VE/00WX identifies it with
exactly B's transpose from the node. This construction never uses H⁰(e), sigma,
or the final transport. We use its underlying section functions: equality on
every object and every section is equivalent to equality of the original module
sheaf maps because forgetting module structure is faithful.

`sectionZero` applies H⁰ to an actual derived point-section map and conjugates
by `mapDerivedCategoryHomologyFunctorIso 0` for exact sections. `pointTransportZero`
uses the actual `frobeniusPointTransportFinite`, and `iotaZero` additionally
conjugates by `directZero` to put a_*M in the source and target. `transportZero`
likewise uses the actual `frobeniusOrdinaryTransportFinite`, not an underived
replacement. All its endpoint comparisons are the same `directZero` and
single/pullback comparisons used for the exchange.

`isoRestriction` and `frobeniusPointRestriction` are the arrows (Y,g)→(Y,id)
and (s,h)→(s,id). `sectionPullback` is restriction along the former; `sigma`
restricts a_*M along the latter. In the dependency's comma-normalized sectionwise
inverse-image model, the subsequent insertion and sheafification are precisely
the canonical identification. `finalRestriction` is the unique arrow to the final
site object, and `toPointSections` restricts along Y×_s s→Y. This is the canonical
Gamma(Y,M)=Gamma(s,a_*M) identification. These definitions use no k-linear
structure on g or h.

Clause-by-clause conclusion:

1. The first conjunct quantifies over every pro-etale `U` of s and every section
   of h⁻¹(a_*M) on U. It says
   `exchangeZero ∘ j_h = a_*(j_g) ∘ underivedMate`, using the actual components
   of `intrinsicUnit` at U and its base change. Because j_u=lambda_u⁻¹, this
   is exactly `a_*(lambda_g) ∘ H⁰(e_M) ∘ lambda_h⁻¹ = B_M` under the explicitly
   constructed canonical identifications. It is a sheaf-level assertion, not
   merely an equality on global sections.
2. The second conjunct says `iotaZero x = j_h (sigma x)` for every section of
   a_*M at the final object of s. This is precisely the node's second formula.
3. The third conjunct says `B(sigma(toPointSections x))` is the restriction of
   `sectionPullback x` along the postcomposed final projection. This is exactly
   `Gamma(s,B) ∘ sigma = p_g` with the canonical final-object identifications.
   The additional restriction on the right is an isomorphism, since Y×_s s→Y
   is an isomorphism, so no information is lost.
4. The fourth conjunct evaluates `transportZero` on `toPointSections x` and
   identifies its value with j_g(p_g(x)), restricted along that same final
   projection. Inverting j_g gives precisely
   `Gamma(Y,lambda_g) ∘ H⁰(tau_M) = p_g`. Its left side is the recorded tau.

Dependency declarations read and used (public imports also retain each recorded
module's more general integral/rational interfaces):

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`,
  `FiniteFieldDatum.geometricFiber`.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing`, and its retained coefficient ring.
- `def-weil-scheme-morphism-properties` is a convention record: the actual
  `Over`, `LocallyOfFiniteType`, `QuasiCompact`, `IsSeparated` declarations are used.
- `Sheaf.AlgebraicGeometry.FrobeniusDetailed`:
  `FiniteFieldDatum.geometricFrobenius`, `FiniteFieldDatum.galoisMap`.
- `Sheaf.SixFunctors.FrobeniusSquareCartesian`:
  `FiniteFieldDatum.frobenius_square_cartesian`.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `ProEt.topology`.
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`: `proEtaleBaseChange`,
  `proEtaleConstantRing`, `proEtaleConstantModuleDirectImage`.
- `Sheaf.Paper.DerivedPullbackTensorHom`: finite pullback, namely the existing
  `sfIntrinsicDerivedPullback` presentation.
- `Sheaf.Paper.SfCommonStageDirectImage` publicly retains
  `SfDerivedDirectImage` / `proEtaleConstantDerivedDirectImage`.
- `Sheaf.Paper.IntrinsicFiniteTorsionConstructibility`:
  `intrinsicFiniteTorsionConstructible` and retained
  `IsConstructibleProEtaleModuleSheaf`.
- `Sheaf.Paper.InverseImagePullbackComparisonDerived` publicly retains
  `inverseImageFiniteComparisonComplex`,
  `inverseImageFiniteIntrinsicPullbackComparison`, and
  `inverseImageFiniteModules` from the recorded finite comparison module.
- `Sheaf.Paper.IsomorphismDerivedPullback`:
  `isomorphismFiniteDerivedPullback_termwise` supplies the interpretation of the
  invertible j and lambda; its site-relabeling interface is retained.
- `Sheaf.Paper.FrobeniusGeometricExchange` retains the specified
  `FrobeniusExchange.finiteExchange` and its unit-preserving tensor presentation.
- `Sheaf.SixFunctors.FrobeniusPointTransport`:
  `frobeniusPointIso`, `frobeniusPointRestriction`, `frobeniusPointTransportFinite`.
- `Sheaf.Paper.PointProEtaleSectionsExact`: `point_proEtale_sections_exact`;
  the existing exact point section comparisons are used through the point fibre.
- `Sheaf.SixFunctors.FrobeniusCohomologyTransport`:
  `frobeniusOrdinaryTransportFinite`, `frobeniusCohomologyModelMap`.
- `def-weil-sheaf-of-modules-category`: the dependency's `SheafOfModules`,
  presented as `proEtaleRingModules` / `integralOperationsFiniteModules`.
- `Sheaf.Paper.CommonStageCompactWeilCohomology` retains ordinary cohomology and
  `sfWeilCohomologyPoint`; ordinary finite cohomology is exactly the point sections
  of the actual finite derived direct image used above.
- `Sheaf.Paper.FiniteCoefficientPoint`: `pointFiniteSections`,
  `pointFibreFiniteLimits`, `pointFibreFiniteColimits` and its actual target model.

The proof-only modules of `preDerivedAdjunctionGeneral` and
`Adjunction.preservesKInjectiveComplexes` are imported for the recorded proof plan.
The continuous site pullback adjunction is the Mathlib
`Functor.sheafPullbackConstruction.sheafAdjunctionContinuous` retained by the
inverse-image module. The existing isomorphism inverse-image module supplies the
specified comma-normalized sectionwise interpretation.

Edge cases checked before writing: n=0 means A_{E,1}; M=0 gives zero maps; empty
Y gives the zero section modules; Y=s includes the point case via the prescribed
geometric fibre identification; disconnected Y requires no chosen component.
Arbitrary finite extensions E are allowed and no unit section of M is selected.
The commuting identity uses semilinear Frobenius, and the Cartesian map and all
restrictions are scheme/site arrows, so no k-linearity assumption is hidden.

Searches performed:

- msearch leanfinder: "Degree zero derived Frobenius exchange mate equals
  underived inverse image section pullback". Eight hits concern closed-monoidal
  Frobenius morphisms, ring Frobenius inverses, or scheme-module identity pullback;
  none is this pro-etale exchange/transport statement.
- msearch loogle: "CategoryTheory.Adjunction,
  CategoryTheory.DerivedCategory.homologyFunctor". No hits (the service does not
  index that qualified homology identifier).
- msearch grep in Mathlib CategoryTheory:
  `exchange.*(zero|Zero)|frobenius.*(sections|Sections)`. No hits.
- msearch leansearch: "H0 of derived direct image base change along a Frobenius
  square equals the inverse image mate on global sections". Eight hits concern
  scheme structural sections, ordinary module direct image and a closed-monoidal
  mate. None supplies the four prescribed pro-etale maps.
- rg in upstream `WeilConjectures` for the node ID and Frobenius exchange/degree
  zero names: no exact statement. The upstream Frobenius trace modules concern
  different operators. rg in `lean/Sheaf` found general etale degree-zero
  exchange statements and Frobenius constructions, but no statement combining
  this finite pro-etale mate, point transport and section restriction. Read the
  relevant recorded Frobenius/point/direct-image modules in full at their used
  declarations. `tools/lean_names_upstream.py show` also exposed no exact match.

Validation: scompile.py checked the sandbox and exact library-path module cleanly
(15.7 s and 25.3 s in the successful run). No lake/global build was run. A finite
point-target derived-category size mismatch was diagnosed against the recorded
transport; the helper reuses its same Grothendieck small model. No hypothesis was
introduced to force universe equality. The delivery dry run and final delivery
checks are run after this report is written.

No STATEMENT-DISPUTED flag, statement correction, dependency repair, or unresolved
mathematical fault remains. Independent review is by the maintainer, as required
by the current direct-delivery brief.

## Second reading by Q06

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
