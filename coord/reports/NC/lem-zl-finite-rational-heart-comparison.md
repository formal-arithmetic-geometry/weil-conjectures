## Worker report

The module `Sheaf.Paper.FiniteRationalHeartComparison` states this node in the namespace
`WeilConjectures.FiniteRationalHeart`. All seven postponed results have named declarations,
source/proof docstrings, and `sorry` proofs. All definitions contain real data. The other
23 declarations expose the supplied comparisons or the actual maps used in these clauses;
they introduce no independent mathematical notion. No mathematical statement was corrected.

Hypotheses and clauses, matched to Lean:

- Finite-field data: `D : FiniteFieldDatum.{u}`; the prime is `l` with `[Fact l.Prime]`
  and `hl : l ≠ D.p`. `E : Type u`, `[Field E]`, `[Algebra (Padic l) E]`, and
  `[FiniteDimensional (Padic l) E]` specify precisely the finite coefficient extension.
  Its ring, uniformizer and quotients are the recorded `Padic.coefficientExtensionIntegers`,
  `Padic.coefficientExtensionUniformizer`, and `Padic.coefficientExtensionRing`.
- Geometric assumptions: `X Y : Scheme.{u}`, each with `Over (Spec (.of D.k))`,
  `LocallyOfFiniteType`, `QuasiCompact`, and `IsSeparated` on its structure morphism;
  `f : X ⟶ Y` with `[IsFinite f]`. `y : Spec (.of D.k) ⟶ Y` is an arbitrary scheme
  morphism: no `IsOver` condition is imposed on it. The fibre is literally `pullback f y`;
  `fibreOver` supplies precisely `pullback.snd f y` as its structure morphism. Its three
  geometric instances are inferred from finite base change.
- The lift index is the subtype `Lifts D f y = {x // x ≫ f = y}`. `lifts_finite` states
  its finiteness. `lift` uses the actual pullback universal property, and `lift_projections`
  states both projections and uniqueness. No nonemptiness hypothesis appears.
- Completed coefficients, strict reductions and exact scalar restriction use the existing
  `scalarReductionSource`, `scalarReductionDerivedExtension`, `scalarReductionDerivedRestriction`
  and `integralDetailedTransport`. `coefficients` gives the equality at every coefficient
  projection and exactness of restriction along the canonical ring isomorphism. The
  currently published detailed and sf definitions have different coefficient encodings
  (a lifted quotient/functions-sheaf encoding versus its normalized constant-sheaf encoding).
  The existing `integralDetailedCoefficientComparison` is normalized at every level and
  identifies them; a false literal equality between these two Lean encodings is not used.
- `categories` states the equivalence of the intrinsic and PBC predicates, an integral
  equivalence with its exact object and arrow formula, and its raw rational equivalence
  with the coefficient-adjusted pure tensor formula. Both raw category definitions keep
  the integral objects and tensor the Hom modules: neither adjoins idempotents. It also
  states localization of both standard halves and integral heart representatives. Its
  variable `W` applies in particular to `X`, `Y`, `pullback f y`, and `Spec (.of D.k)`.
- The supplied functor is `T`, with additive, integral-linear, shift and triangulated
  structures, and `hT` for both integral standard halves in every degree. These are the
  node's exact integral functor and t-exactness assumptions. `H` names the tower direct
  image along `h`; its raw transport only requires its additive integral-linear structure.
- `TowerComparison` retains a genuine `SfIntegralDirectImage`, every projection, and
  an isomorphism intertwining every projection. Its `reduction` is scalar adjunction of
  precisely that projection, rather than an arbitrary reduction comparison. `cT` and
  `cH` are the stipulated identifications with these towers. `Restrictions.tower_natural`
  and `.fibre_tower_natural` spell out naturality of these identifications, term by term.
- `Restrictions.beta` is the stipulated natural isomorphism `T ⋙ pull y ≅ pull v ⋙ H`.
  `.rho` and `.rho_natural` are the stipulated natural finite biproduct isomorphism.
  `.beta_reduction` uses the actual exchange mate `finiteExchange`; `.rho_reduction`
  normalizes the composite to every finite counit-germ `finiteGerm`. They quantify over
  every good complex representative and every positive level (Lean index `n` means
  exponent `n + 1`). `finiteAdj` is the recorded inverse-image/direct-image adjunction,
  transported by its canonical sectionwise direct-image isomorphism. Its counit and the
  recorded `integralFiniteCanonicalPullbackComposition` define the two reduced arrows.
- `extension` is precisely `ScalarLocalization.transport`, keeping the integral object
  and tensoring its Hom maps. `raw_extension` states uniqueness among additive linear
  extensions on the integral generators and exactness with the supplied shift comparison
  tensored with one. Thus the tower-normalized `T` has precisely the node's prescribed
  rational direct image; no separate arbitrary direct-image functor is introduced.
- `rational_heart_comparison` first states preservation of both rational halves, then
  the t-exactness of the actual `y`, `v`, and every `x` pullback. It supplies the actual
  restriction `Fh` to the recorded full constructible hearts, with the commuting inclusion
  equality and preservation of finite limits and colimits (exactness).
- The theorem supplies `βE` as a derived natural isomorphism, with equality to the raw
  localization of the given `R.beta`, conjugated only by `localPullbackObjectIso`.
  It supplies the derived isomorphism `ρE`, with every biproduct projection equal to the
  localization of the given `R.rho` projection. It also states its naturality for all
  rational morphisms, including fractions. These are derived statements before H0.
- `ordinaryProjection` exposes the exact Roos witness selected by the dependency's
  `integralImage`. `OrdinaryComparison` preserves all its projections. `ordinaryIso`
  localizes that comparison and identifies the middle term with the existing
  `rationalImage`; no new definition of ordinary cohomology is used.
- `pointH0` is exactly `pointRationalFibre ⋙ DerivedCategory.coefficientFdCohomology E 0`.
  The two concluding isomorphisms `a F`, `b F` use the actual rational pullbacks and the
  existing `rationalOrdinaryCohomology ... 0`. Their formulas are respectively pointH0
  of `βE` followed by the normalized ordinary comparison, and its inverse followed by
  pointH0 of `ρE` and the canonical finite biproduct comparison. Thus the displayed arrows,
  and not only their endpoints, are specified. The last three clauses assert naturality
  of each arrow and E-linearity of the middle morphism convention `ordinaryMap`.
  The other arrows are morphisms in `ModuleCat E` and hence E-linear themselves.
- `point_sections` states exact integral point sections, vanishing outside degree zero
  on rational heart objects, preservation of the displayed biproduct both before and
  after H0, and the E-linear morphism formula. The point-derived target lacks a registered
  general biproduct instance; the assertion supplies the needed `HasBiproduct` witness
  and asserts that its actual canonical comparison is invertible, without assuming it.

Dependency declarations used (module: declarations):

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`: coefficient integers,
  uniformizer, quotient ring, and `Padic.finite_coefficientExtensionRing`.
- `Mathlib.AlgebraicGeometry.Morphisms.Finite`: `AlgebraicGeometry.IsFinite` and its
  finite-base-change/finite-type/separatedness instances; scheme properties use their
  individual Mathlib classes, as required by the dependency convention node.
- `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`: completed coefficient maps;
  `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, through the recorded imports.
- `Sheaf.Paper.SfIntegralConstructible`: `sfIntegralConstructible`,
  `sfIntegralConstructibleCategory`.
- `Sheaf.Paper.IntegralDerivedOperationsOnSlices`: the public integral operations and
  strict reductions, with `Sheaf.Paper.IntegralPullbackComposition` supplying
  `integralPullbackReductionIso` and `integralFiniteCanonicalPullbackComposition`.
- `Sheaf.Paper.SfDerivedDirectImage`: `SfIntegralDirectImage`, `sfDirectImageTerm`,
  `sfFiniteDerivedDirectImage`, `derivedScalarExtensionRestrictionAdjunction`.
- `Mathlib.FieldTheory.IsAlgClosed.Basic`: the algebraically closed field convention;
  `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`: `Limits.pullback`.
- `Sheaf.Paper.IntegralUniformCoefficient`: `PbcIsBoundedConstructibleComplete`,
  `PbcBoundedConstructibleComplete`, and `pbcIntegralDatum`.
- `Sheaf.Paper.SfRationalizationKaroubi`: `sfRationalConstructibleCategory`,
  `sfRationalConstructibleLocalization`, `sfRationalCoefficientEquiv`.
- `Sheaf.Paper.PbcRationalCategory`: `PbcRationalCategory`, `pbcUniformizer`.
- `Sheaf.Paper.SfConstructibleHeart`: integral/rational standard classes,
  `sfRationalHeartProperty`, `sfRationalHeart`, `sfRationalStandardTStructure`.
- `Sheaf.Paper.FiniteCoefficientPoint`: `pointRationalFibre`, `pointIntegralSections`.
- `Sheaf.Paper.LocalFrobeniusTrace`: `localPullbackObjectIso` and the rational derived
  stalk convention (pullback to the point then its recorded point fibre).
- `Sheaf.Paper.CommonStageCompactWeilCohomology`, publicly exposing
  `OrdinaryCompactCohomology`: `integralImage`, `rationalImage`,
  `rationalOrdinaryCohomology`.
- Additional landed definition dependencies: `def-a1-constructible-pullback-residue-units`
  gives `constructiblePullbackResidueUnits` in `ConstructiblePullbackTExact`;
  `def-trf-integral-pullback-composition-family` gives the reduction/composition comparisons;
  `def-pur-proetale-global-section-maps` gives the sectionwise derived direct image and
  `proEtaleUnitLerayDirectImageIso` in `ProEtaleUnitLerayChainFormula`.
- `Sheaf.Paper.PbcRationalTransport`: `ScalarLocalization.transport`, its uniqueness and
  exactness APIs, and `pbcRationalCoefficientEquiv`.
- Proof imports: `IntegralStratifiedPerfectCharacterization` and its normalized
  `integralDetailedTransport`; `LocalizedTStructure`; upstream triangulated t-structure
  homology/heart triangle criterion; `IntegralPullbackCompletedComparison`;
  `PointProEtaleSectionsExactOfUniverses`; `IntegersLocalizationUniformizer`; upstream
  finite-type dimension bounds. The not-yet-recorded proof dependency
  `lem-per-integral-pullback-bounds` has no module to import; no statement dependency
  waits on it, and the current delivered theorem states the required pullback conclusion.

Edge cases checked: an empty fibre has `Finite` lifts but no `Nonempty` requirement;
all biproducts, including the empty one, are canonical finite biproducts. Zero objects
and zero arrows satisfy the exactness and normalization formulas. The smallest quotient
is `n = 0` in the Lean indexing, i.e. O_E/varpi, not the exponent-zero ring. Arbitrary
non-k-linear geometric maps `y` and lifts `x` remain allowed; the fibre's structure map
is its second projection. No equality of site and coefficient universes is imposed.
The finite coefficient field E and all schemes are in the project's common universe u,
with the existing u+1 coefficient-sheaf lift retained by the imported APIs.

Searches actually run through `batch2/msearch.py` and direct source search:

- LeanFinder: “Rational localization of integral constructible categories preserves
  t exact functors and the specified geometric fibre restriction maps”: eight hits
  about condensed/perfectoid categories and `AdicCompletion.map_exact`; no exact match.
- Loogle: `"IsLocalization", "IsTriangulated"`: zero hits.
- Mathlib grep: `rational.*[Hh]eart|[Hh]eart.*[Cc]omparison` under CategoryTheory: zero hits.
- LeanSearch: “Raw rational localization of a constructible integral category and exact
  point sections preserve normalized geometric fibre restriction maps”: eight hits,
  including `ModuleCat.instPreservesFiniteLimitsLocalizationLocalizedModule_functor`
  and generic localization finite-product lemmas; no project comparison or fibre maps.
- `rg` of `lean/WeilConjectures` and `lean/Sheaf` for rational-heart comparisons found
  the downstream `ZlFiniteAdicDirectImage` interface and unrelated heart comparisons.
  That downstream theorem depends on this node, so cannot be imported as its proof or
  used as an existing declaration for this node. Its ordinary-projection construction
  confirms how to expose the same dependency-selected Roos vertex. There is no upstream
  duplicate statement. `grep -rn lem-zl-finite-rational-heart-comparison lean/WeilConjectures`
  returned no hits. The source and dependency declarations were opened and read.

Sources read: Bhatt–Scholze PDF, Proposition 6.8.14 and Remark 6.8.15 (pages 61–62),
and the current `literature/blueprint/latest/.../lem-zl-finite-pushforward.proof.md`.
No STATEMENT-DISPUTED finding or node correction.

## Second reading by NC

The dispatcher expressly forbids starting other agents and assigns the independent
review to the maintainer. This section records my final in-session rereading, not a
claim of a second worker's independent review. I reread the node and the full module,
matching the hypotheses and clauses as above. I caught and repaired omitted explicit
uniqueness/exactness of the raw extension, naturality for rational morphisms, point
sections before H0, the unique-lift equations, and the normalized completed-coefficient
projections. I also checked that the ordinary middle term is the dependency's actual
object and that both final maps are specified by equations, not mere existence of
isos. The independent maintainer review remains to be performed on this delivery.
