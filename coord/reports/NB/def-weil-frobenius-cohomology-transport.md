## Worker report

`lean/Sheaf/SixFunctors/FrobeniusCohomologyTransport.lean` defines the two actual
Frobenius cohomology transports for finite, completed integral, rational and
algebraically closed coefficients, and their induced maps in every integer degree.
Every construction has real data. There are no new theorems, axioms or `sorry`s.
The node's natural-language statement, dependencies and proof fields are unchanged.

The saved packet was retained as the starting point and dry-run first. Its first
compiler errors were missing scheme namespaces. The next compiler pass exposed
two unused hypotheses. The accompanying self-check found substantive faults:
the point-transport component was mapped by the fibre functor twice, and the
operation datum admitted arbitrary functors and exchange maps without identifying
them with the recorded geometric operations. The repaired module retains the
specified two-arrow composite but instantiates both arrows from the dependencies.
The former unconstrained datum and unused coefficient-ring binder are removed.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The finite-field tuple is `D : FiniteFieldDatum.{u}`. Its actual `k₀`, algebraic
  closure `k`, inclusion and geometric fibre are used throughout.
- The prime is `l : ℕ` with `[Fact l.Prime]`; `hl : l ≠ D.p` is used by the point
  transport, the completed operations and the inherited stalk-invertibility data.
- A finite coefficient field is `E : Type u` with `[Field E]`,
  `[Algebra ℚ_[l] E]` and `[FiniteDimensional ℚ_[l] E]`. The finite and integral
  constructions do not depend on an embedding of E in the coefficient closure.
  For algebraically closed coefficients the actual finite fields of definition
  are precisely `K.stage`, with the recorded coefficient model
  `AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω K.stage` and its
  `Shrink.algEquiv` identification with the subfield of Ω.
- The positive coefficient exponent is represented by `n + 1`, `n : ℕ`.
  `Nat.succ_pos n` supplies the positivity proof. This covers every exponent
  at least one, including exponent one when `n = 0`.
- The four choices of Λ are separate declarations, rather than an unrestricted
  `[CommRing Λ]`: `frobeniusCohomologyTransportFinite`,
  `frobeniusCohomologyTransportIntegral`,
  `frobeniusCohomologyTransportRational`, and `frobeniusCohomologyTransport`.
  Their inputs are respectively the full subcategory of
  `intrinsicFiniteTorsionConstructible`, `sfIntegralConstructibleCategory`,
  `sfRationalConstructibleCategory`, and
  `generalAlgebraicallyClosedConstructibleCategory`.
- The model is `Y₀ : Over (Spec (.of D.k₀))` with
  `[LocallyOfFiniteType Y₀.hom]`, `[QuasiCompact Y₀.hom]` and
  `[IsSeparated Y₀.hom]`. These are exactly separated finite type. The helper
  `frobeniusCohomologyModelMap` is its actual structure arrow over k₀.
- `Y` is literally `(D.geometricFiber Y₀).left`; `a_Y` is its `.hom`.
  `s` is literally `Spec (.of D.k)`. No abstract replacement scheme is supplied.
  The necessary finite-type and separated instances on `a_Y` are inherited by
  base change; they are not additional hypotheses.
- `g_Y` is the recorded `FrobeniusExchange.galois D Y₀`; `g_s` is
  `(frobeniusPointIso D).hom`. The direct model uses the final structure-square
  clause of `D.frobenius_square_cartesian`. Its `.w` gives the exact required
  equation `g_Y ≫ a_Y = a_Y ≫ g_s`.
- The retained compactification `c₀ : Compactification Y₀.hom` is a choice of
  the compact-support presentation already required by the exchange dependency,
  not a properness hypothesis. `frobeniusCohomologyCompactification` base changes
  its actual open part and middle scheme. Its proper part is the middle scheme's
  structure map to Spec k. The compact support model uses the middle model's
  geometric Frobenius and the recorded Cartesian open square. No lift of
  Frobenius, square, comparison or exchange map is supplied as an arbitrary input.
- Ordinary finite transport applies `frobeniusPointTransportFinite` to the actual
  `proEtaleConstantDerivedDirectImage a_Y` object, then applies the point-sections
  functor to `FrobeniusExchange.finiteExchange`. This is the ambient adjunction
  mate in intrinsic pullback coordinates. Thus the result is exactly
  `iota_(Ra_*M) ≫ Fib(FrEx_*(M))`.
- Compact finite transport uses the same first arrow at
  `sfIntrinsicCompactSupport c M`, followed by the fibre of `finiteCompact`.
  The `openSquareDerivedPullbackModel` isomorphisms merely express that recorded
  tensor-pullback exchange in the intrinsic coordinates used by the point map.
  Thus the result is `iota_(Ra_!M) ≫ Fib(FrEx_!(M))`, with the retained c.
- Integral transport uses `modelFunctor` and `modelExchange` with the actual
  structure map, actual two Frobenii and either of the two constructed support
  models. The first arrow is `frobeniusPointTransportIntegralConstructible`;
  the second is `(pointIntegralFibre ...).map` of the integral exchange component.
  The imported exchange constructs its system map before evaluation and applies
  its specified alpha-total-limit-beta recipe. No map is selected by a finite
  reduction property alone.
- Rational transport uses `modelRationalFunctor` and `modelRationalExchange`,
  the literal scalar-localization constructions of that same integral recipe.
  Its first arrow is `frobeniusPointTransportRational`. The only intervening
  identification is the equality of the uniquely normalized rational-pullback
  object with its integral representative, from
  `rationalDerivedPullback_existsUnique`. No rational object is reduced modulo
  a uniformizer, and no Karoubi completion is introduced.
- Algebraically closed transport applies the rational composite at the object's
  own actual stage `K.stage`. `frobeniusCohomologyCoefficientExtension` then
  realizes the stage morphism in D(Ω) by exact scalar extension. This is the
  realization of the common-stage point-fibre morphism, retaining the specified
  finite-stage representative. The source scheme universe u and closure universe
  v remain independent. The two intermediate coefficient ULifts and the module
  ULift have canonical ring equivalences; restriction along those equivalences
  and exact field scalar extension supply all their data. The final carrier is
  `ModuleCat.{max u v} Ω`, with the standard derived localization. This canonical
  coefficient/size transport avoids restricting the closure to the point-fibre
  dependency's single-universe presentation.
- The naturality clause is inherited from the point components, the exchange
  natural transformations and exact coefficient realization. The recorded
  `lem-weil-frobenius-point-transport-natural` states naturality of the point
  components and their scalar compatibility; the exchange dependency supplies
  the natural and scalar-compatible exchanges. The module introduces no new
  naturality hypothesis and no invertibility assumption.
- `frobeniusCohomologyMapFinite`, `frobeniusCohomologyMapIntegral`,
  `frobeniusCohomologyMapRational`, and `frobeniusCohomologyMap` apply exactly
  the corresponding recorded homology/coefficient-cohomology functors to the
  two arrows. Their degree binder is `i : ℤ`, including negative degrees.
  Invertibility remains the separate cohomology-transport-isomorphism node.

Dependency declarations read and reused:

- `Sheaf.Paper.FiniteFieldFiber`: `FiniteFieldDatum`, `FiniteFieldDatum.geometricFiber`.
- `Sheaf.Paper.IntrinsicFiniteTorsionConstructibility`:
  `AlgebraicGeometry.Scheme.intrinsicFiniteTorsionConstructible`.
- `Sheaf.Paper.SfIntegralConstructible`: `sfIntegralConstructibleCategory`.
- `Sheaf.Paper.SfRationalizationKaroubi`: `sfRationalConstructibleCategory`.
- `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients`:
  `generalAlgebraicallyClosedConstructibleCategory`, its actual stage and coefficient model.
- `def-weil-scheme-morphism-properties` is a convention node. Its separated and
  finite-type meanings are the Mathlib morphism-property instances above.
- `Sheaf.AlgebraicGeometry.FrobeniusDetailed`: `FiniteFieldDatum.geometricFrobenius`,
  the recorded geometric coefficient action, reused as `FrobeniusExchange.galois`.
- `Sheaf.SixFunctors.FrobeniusSquareCartesian`:
  `FiniteFieldDatum.frobenius_square_cartesian`, including its final Spec k square.
- `Sheaf.Paper.DerivedPullbackTensorHom`: `finiteDerivedPullback`,
  `constructibleIntegralPullback`, `rationalDerivedPullback_existsUnique`.
- `Sheaf.Paper.SfCommonStageDirectImage` retains the actual derived direct-image
  interfaces. The exchange's `modelFunctor` / `modelRationalFunctor` select its
  integral system direct image / raw localization for the direct recipe.
- `Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport`:
  `AlgebraicGeometry.Scheme.sfIntrinsicCompactSupport`.
- `Sheaf.Paper.FiniteCoefficientPoint`: `pointFiniteSections`, `pointIntegralFibre`,
  `pointRationalFibre`, and the point-coefficient categories.
- `Sheaf.Paper.CommonStageCompactWeilCohomology`: `sfWeilCohomologyPoint` and the
  publicly retained `DerivedCategory.coefficientFgCohomology` /
  `DerivedCategory.coefficientFdCohomology` interfaces. Ordinary/compact cohomology
  is the fibre of the respective operation, as in the node.
- `Sheaf.Paper.IsomorphismDerivedPullback` supplies the finite/integral
  isomorphism-preservation interface used by the recorded constructible pullbacks.
- `Sheaf.SixFunctors.FrobeniusPointTransport`: `frobeniusPointIso`,
  `frobeniusPointPrimeInvertible`, `frobeniusPointTransportFinite`,
  `frobeniusPointTransportIntegralConstructible`, `frobeniusPointTransportRational`.
- `Sheaf.Paper.FrobeniusGeometricExchange` publicly retains `finiteExchange`,
  `finiteCompact`, `modelFunctor`, `modelExchange`, `modelRationalFunctor`,
  `modelRationalExchange`, `geometricCompactification`, `fiber_finiteType`,
  `zlCompactificationMiddle` and `zlCompactificationOpen`.

The coefficient-realization helper uses Mathlib's `ModuleCat.uliftFunctor`,
`ModuleCat.restrictScalars`, `ModuleCat.extendScalars`, its scalar adjunction,
flat-field exactness and `Functor.mapDerivedCategory`. Its purpose is canonical
size transport for this node's cohomology arrows, authorized by the brief's
owning-node helper rule; it does not replace any coefficient category definition.
All helper declarations are listed in `lean.declarations` with source/blueprint docstrings.
No new nodes or dependency-record changes are needed.

Edge cases checked: the empty scheme and zero object impose no nonemptiness
condition; the exponent-one case is `n = 0`; every `i : ℤ`, including a vanishing
or negative degree, is present. A nonproper separated finite-type scheme is
allowed because only the chosen compactification's proper part is proper.
Ordinary and compact operations remain separate. The input object can have any
finite coefficient stage; its own stage is retained. The final scalar transport
permits independent u and v, and the small pro-etale site's object and morphism
universes have not been identified.

Searches: the saved `msearch.py` leanfinder query "transport of ordinary and
compactly supported etale cohomology along geometric Frobenius" returned eight
unrelated isocrystal/Witt-vector hits. The saved loogle query "Frobenius cohomology
transport, geometric Frobenius exchange" returned no hit (unknown identifier
Frobenius). The repair reran `msearch.py ... grep
'frobenius.*[Cc]ohomology|[Cc]ohomology.*[Tt]ransport' AlgebraicGeometry`, with
zero hits. `rg` for the transport names in the source project and `lean/Sheaf`,
for this node id in the source project, and for Frobenius/cohomology transport in
Mathlib's CategoryTheory returned no match. Existing point transport and exchange
constructions were reused; their composite had no existing declaration.

Validation: all 18 declarations and the single delivered module compile through
`scompile.py`, both as the sandbox file and as the library-path file, with no
errors or warnings. No global build or live-source edit was performed. The final
delivery dry run is recorded by the delivery tool.

## Second reading by NB

This is the resumed worker's self-check; the maintainer supplies the independent
review. Reading the node against the saved file exposed the double fibre-map and
unconstrained-operation defects described above. The current file uses the actual
geometric fibre, structure map, point Frobenius and geometric Frobenius throughout.
Finite/integral/rational/Qbar coefficient domains are the recorded domains, and
all positive exponents and integer degrees are covered. The first arrow in each
recipe is the recorded point transport itself; only the exchange is mapped by the
point fibre. Both compactification squares refer to the retained finite-field
model. Rational normalization and the Qbar size transport are explicit canonical
constructions. No arbitrary map, closure-universe equality, properness assumption,
invertibility assertion or new postponed proof is present. The repaired source
and node record were checked together; no natural-language statement correction
was necessary.
