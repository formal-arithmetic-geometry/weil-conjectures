## Worker report

The module Sheaf.Paper.TwistFrobeniusScalar states
WeilConjectures.TwistFrobeniusScalar.twist_frobenius_scalar, with every theorem proof `sorry`.
All helper definitions have real data. This packet repairs the return on immutable
head a229ddce61cb: the compatibility clauses now name the actual canonical maps,
assert their invertibility, and give their individual Frobenius squares. The saved
repair was retained; its first required dry run exposed remaining integral-section
interface errors, which were repaired in this sandbox. Nothing is proved in stage 2.
Sources read: the current node, all six statement-dependency node statements and Lean
records, their source declarations, Weil I PDF pp. 280–281, (2.2), Weil II PDF p. 150,
(1.1.7), and main-20261015/blueprint/sec-six-functors-basics/sk-def-purity-conv/
def-weil-frobenius-coefficient-twists.md. The blueprint specifies the inverse-q action
on E(1), signed powers, finite reduction and scalar extension. The DAG expands its
point-cohomology formulation without changing that convention.

Hypotheses and clauses, matched with Lean:

- The global finite-field tuple is `D : FiniteFieldDatum.{u}`. Its fields retain
  p prime, a positive, q = p^a, the finite field of cardinality q, and its specified
  algebraic closure and inclusion. `l : ℕ`, `[Fact l.Prime]`, `hl : l ≠ D.p`
  give exactly the coefficient-prime conditions.
- E is `Type u`, with `Field E`, `Algebra (Padic l) E`, and
  `FiniteDimensional (Padic l) E`. Its valuation ring, chosen uniformizer and
  quotient use `Padic.coefficientExtensionIntegers`, `coefficientExtensionUniformizer`
  and `coefficientExtensionRing`. Every positive finite exponent is n+1, n : ℕ.
  Ω has its own universe v, `Field`, `Algebra (Padic l)` and `IsAlgClosure` instances.
  Each embedding E into Ω is quantified in the final clause, so the chosen embedding
  of the finite extension in the closure is included, rather than silently fixed.
- `sfWeilCohomologyPoint D` is Spec(k₀) over itself with identity map. Its
  `D.geometricFiber` is the canonical pullback model for s = Spec(k); the existing
  point functors use its projection to Spec(k). `geometricPoint` only abbreviates
  this very recorded geometric fibre; it introduces no replacement point.
- `m : ℤ` includes all signed twists. `finiteLine` is the published signed finite
  sheaf under `singleFunctor 0`; `integralLine` is `sfIntegralTwistingCoefficient`;
  `rationalLine` and `qbarLine` use the actual published rational/common Weil lines.
  Their structures are the canonical root/scalar/dual structures, not supplied actions.
- `finiteSections`, `integralSections`, `rationalSections`, `qbarSections` are the
  recorded Frobenius cohomology functors with compact=false and the identity model
  compactification. No assumption of an arbitrary comparison or cohomology functor
  is added. The compactification parameter only presents the same ordinary component.
- `finiteF` is H⁰ of `frobeniusOrdinaryTransportFinite` followed by sections of the
  finite theta. The source of that transport uses the intrinsic pullback; the line
  map uses tensor pullback. `openSquareDerivedPullbackModel.inv.app` is the existing
  section/unit-normalized coordinate isomorphism between them. This repairs the
  retained attempt's compile error and preserves the specified canonical action.
- `integralF` uses `frobeniusTransportIntegral` for the direct model followed by
  `integralDerivedLineMap`, whose completed-to-ordinary comparison is normalized on
  good representatives. `rationalF` is the ordinary transport followed by the
  rational Weil structure. Reading GlobalGeometricFrobenius.lean shows it is exactly
  the first component of `globalGeometricFrobenius`, and applying H⁰ is exactly its
  `globalGeometricFrobeniusOnCohomology` first component at i=0.
- `qbarF` uses the recorded common-stage transport, its prescribed source/target
  object equalities, and the common Weil structure. Its realization lives in the
  standard D(Ω), retaining independent site/coefficient universes.
- Each of the first four conjuncts asserts `∀ i : ℤ, i ≠ 0 → Subsingleton (…H… i)`:
  both positive and negative cohomology vanish. Each rank-one assertion is a
  `Nonempty` linear equivalence from H⁰ to its coefficient ring. This is existence
  of a basis, not data chosen to define a Tate object or an action.
- In each coefficient case the elementwise equation `(…F…).hom x = scalar … D.q m • x`
  states multiplication by q^(-m). `scalar` uses `Ring.inverse` of q for a
  nonnegative exponent and the ordinary positive power for a negative exponent.
  Since l ≠ p, q is a unit in Z_l and in its coefficient images. The unit inverse
  is therefore exactly the image of the inverse in Z_l. This also works in the
  quotient ring, where field division would be ill-typed. At m=0 the formula is 1;
  at m=1 it is q inverse; at m=-(d:ℤ), d≥0, it is q^d. Thus the stated particular
  cases are instances of the single formula, including d=0.
- The fifth conjunct is `∀ n, CoefficientCompatibility ... (reductionH ... n m)`.
  Here `CoefficientCompatibility c M N f g e` means exactly `IsIso e ∧
  (ModuleCat.extendScalars c).map f ≫ e = e ≫ g`. Thus invertibility is asserted
  for the named canonical map, rather than for an unspecified isomorphism.
- The sixth conjunct names `localizationH`, using the actual valuation-ring
  inclusion `localization`. The target and its Frobenius use the same published
  `ModuleCat.uliftFunctor` to match the prescribed integral carrier size.
- The seventh conjunct names `scalarRationalH` for every finite extension L and
  Padic-algebra embedding E → L. The eighth names `scalarQbarH` for every E → Ω.
  Identity embeddings and all ramification remain included. Each clause asserts
  `IsIso` of that comparison itself and its precise intertwining equation.
  `extendScalars` uses S tensor_R M; tensor commutation identifies this with the
  node's M tensor_R S.

Canonical maps and normalization, repairing L H3/H5:

1. `scalarSheafLine_existsUnique` pins the integral sheaf comparison on every
   completed scalar tensor to `s • twistScalarMaps(x)`. `scalarIntegralLine_existsUnique`
   pins its derived completed version by `completedScalarComparison` and the actual
   `completedScalarCounit` on the single K-flat signed line. `scalarRationalLine`
   is its raw localization, inserting the published scalar-extension object equality.
   `scalarRationalSections` then composes `frobeniusCohomologyRationalScalar` with
   sections of that very line comparison. The recorded first factor is constructed
   from `frobeniusCohomologyIntegralScalar`, `pointRationalFibreScalarIso` and
   `pointRationalSectionsScalarExtensionIso`. `scalarRationalH` applies its H⁰,
   preceded by the recorded exact `fieldDerivedHomologyIso`.
2. `scalarQbarSections` extends the inverse of this rational comparison from the
   least finite coefficient stage, then applies `frobeniusCoefficientTower` and
   the recorded `frobeniusCohomologyQbarSourceEq`. The least-stage embedding into E
   is uniquely pinned by its composite with E → Ω (`baseEmbedding_existsUnique`).
   The Qbar functor's representative maps are the published
   `frobeniusCohomologyRealizedComparison` composites. Thus this construction uses
   that actual common-stage realization, with no arbitrary realization or basis.
   `coefficientModulesIso_existsUnique` pins the ordinary/size-lifted tensor
   comparison on pure tensors. `scalarQbarH` follows it by the exact
   tensor/homology comparison and H⁰ of `scalarQbarSections`. Universes u and v
   remain independent.
3. `localizationTensorIso_existsUnique` identifies the ordinary localization tensor
   with `pointIntegralToField` followed by `pointFibreCoefficientDown`, by the
   formula a tensor x ↦ up(a) tensor x. `localizationH` then uses the exact tensor
   and homology comparisons, `pointFibreRationalDownIso`, and the inverse of
   `pointRationalNormalization`, including its specified size-descent counit.
   `integralPointSections_eq` records the equality of the ordinary integral sections
   object and the integral representative retained by raw rational localization;
   its proof docstring expands both recipes. `integralPointSectionsIso` is exactly
   `eqToIso` of that equality. This identification connects the source to the
   recorded rational normalization without replacing it by a chosen line map.
4. `signedQuotients_existsUnique` retains `adicPurityRootQuotients` on every
   nonnegative twist and pins the negative maps by evaluation on the positive
   signed line. `reductionSheafLine_existsUnique` balances these actual quotient
   maps: a tensor x ↦ a times quotient(x). `reductionDerivedLine_existsUnique`
   specifies its hom literally by `scalarReductionCounit` on the single K-flat
   line, the single-functor comparison, and that balanced map. `reductionOperation`
   uses the whole-system `reductionEvaluation`, `operationReduction` and
   `systemDirectEvaluation` before that line identification. `reductionSections`
   applies exact point sections to `sfDerivedReductionUnit` (the unit used by
   `sfIntegralReductionTower`), then the identity-on-sections restriction comparison
   `pointUnitIntegralSectionsRestrictionIso`, and the recorded direct-image mate.
   `reductionH` takes H⁰ and balances using `extendRestrictScalarsAdj`. No flatness
   of the quotient is assumed: invertibility of this particular balanced map is
   asserted by the main theorem, as proved by its generator argument.

Every auxiliary existence theorem is unique by its displayed tensor/evaluation
normalization; its chosen data is determined, rather than selected from a mere
existence statement. These helpers belong to this node's line/cohomology comparison
content and are all listed in `lean.declarations`. Each postponed helper is a named
theorem with this node's blueprint tag and a complete proof docstring. There is no
new independent notion or additional hypothesis. In particular the old universally
quantified-map formulation and the report's defense of it have been removed.

Dependency declarations used (source signatures/docstrings read):

- Sheaf.Paper.FiniteFieldFiber: `WeilConjectures.FiniteFieldDatum`,
  `.geometricFiber`, `.CoefficientDatum`.
- Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted:
  `sfIntegralTwistingCoefficient`, `sfIntegralTwistingObject`,
  `sfRationalTwistingCoefficient`, `sfQbarTwistingCoefficient`; this imports the
  prior detailed finite/root constructions, including `finiteCoefficientTwist`.
- Sheaf.Paper.FrobeniusCoefficientTwistsCanonical:
  `FrobeniusCoefficientTwists.finiteDerivedLineMap`, `.integralDerivedLineMap`,
  `.rationalWeilLine`, `.commonWeilLine`; their signatures retain the canonical
  finite, completed, rational and common-stage pullbacks and signed line maps.
- Sheaf.SixFunctors.FrobeniusCohomologyTransport:
  `frobeniusOrdinaryTransportFinite`, `frobeniusTransportIntegral`,
  `frobeniusCohomologyTransportRational`, `frobeniusCohomologyTransport`.
  Its reexported FrobeniusCohomologyTransportIso module supplies the four actual
  cohomology functors and Qbar source/target equalities.
- Sheaf.Paper.CommonStageCompactWeilCohomology:
  `sfWeilCohomologyPoint`; its retained OrdinaryCompactCohomology construction
  supplies finite, integral, rational and common-stage ordinary cohomology.
- Sheaf.Paper.GlobalGeometricFrobenius:
  `globalGeometricFrobenius`, `globalGeometricFrobeniusOnCohomology`.
- Sheaf.Paper.PointSectionsScalarExtension: `pointRationalSectionsScalarExtensionIso`;
  Sheaf.Paper.PointReductionUnits: `pointUnitIntegralSectionsRestrictionIso`;
  Sheaf.Paper.AdicPurityRootComparisons: `adicPurityRootQuotients`;
  Sheaf.Paper.FiniteCoefficientPoint: `pointIntegralFibre`,
  `pointFibreRationalDownIso`, `pointRationalNormalization`.
- Mathlib: `DerivedCategory.homologyFunctor`, `ModuleCat.extendScalars`,
  `ModuleCat.uliftFunctor`, `LinearEquiv`, `Ring.inverse`, `Ideal.Quotient.mk`,
  `ULift.ringEquiv`. The existing
  `AlgebraicGeometry.Scheme.openSquareDerivedPullbackModel` supplies the finite
  canonical coordinate change. All stated proof-dependency modules are imported
  without public; their proof route is transcribed step by step in the docstring.

Edge cases checked: m=0, m=1, m negative, d=0, n+1=1, l=2 with p odd,
ramified E (quotient uses varpi_E, not l), arbitrary finite coefficient extensions,
identity embeddings and E→Ω embeddings, all negative cohomological degrees, and
independent u/v for the common-stage coefficients. No zero quotient is introduced
because the node only allows positive exponents. No finite-field arithmetic action
is substituted for geometric Frobenius; the source explicitly defines it as inverse.

Searches performed and retained in searches.jsonl:

- Loogle, `"cyclotomicCharacter"`: 12 hits, cyclotomic and modular character
  declarations, none states derived point cohomology for these coefficient objects.
- LeanFinder, `Geometric Frobenius acts on Tate twist cohomology of an algebraically
  closed finite-field point by q to the minus m, compatible with finite reduction
  and scalar extension`: 8 hits, arithmetic Frobenius, finite-field Frobenius and
  Witt isocrystals; no exact match.
- Mathlib grep, `TateTwist|tateTwist|frobenius.*cyclotomicCharacter|cyclotomicCharacter.*frobenius`:
  zero hits.
- LeanSearch, `Cohomology of Tate twists at a geometric point with geometric
  Frobenius scalar q^(-m)`: 8 hits, Witt-vector/perfection Frobenius; no exact match.
- Current LeanFinder query, `Geometric Frobenius on cohomology of Tate twists of an
  algebraically closed point is multiplication by q to the minus m`: 8 hits,
  WittVector.StandardOneDimIsocrystal.frobenius_apply and arithmetic/finite-field
  Frobenius. These have different objects; none identifies the canonical operators here.
- Direct rg on the specified upstream WeilConjectures, current lean/Sheaf and
  dag/lean_names_upstream.json for TateTwist/tateTwist/twist_frobenius_scalar/
  TwistFrobeniusScalar. Upstream FrobeniusModule.tateTwist rescales an operator
  by definition; HasTateTwist is an abstract system. Neither proves the root-defined
  coefficient line's actual transport operator. No existing complete statement found.
- Required upstream grep by the exact item id returned no hits.

Validation: all delivered files are checked through scompile.py, then through the
prescribed deliver2.py dry run. The first saved-packet dry run failed on the
integral representative identification and tensor/H⁰ endpoint sizes; those were
repaired. The final compile and dry-run results are recorded below. Every variable
and universe is explicit; autoImplicit and relaxedAutoImplicit are disabled.
No statement correction, new DAG node or dependency-module repair was needed.
There is no STATEMENT-DISPUTED finding. Only the node's lean field changes.

## Second reading by Q94

This is the dispatcher's second source-reading pass by the same worker; no subagent
was started, as this brief explicitly requires. Independent review follows delivery.
Read the saved report first and ran its required initial dry run before editing.
Compared the return's description of a229ddce61cb with the saved Lean and current
read-only DAG/source records. The saved Lean already contained most of the repair,
while its node signature and report still described the returned formulation.
Retained that work, fixed the compile diagnostics, and regenerated the attachment
from the final file on the current DAG record.

Reopened the node and checked all eight conjuncts against the final theorem. The
first four retain the accepted vanishing in every nonzero integer degree, rank-one
H⁰ and q^(-m) scalar clauses for finite, integral, rational and Ω coefficients.
The last four now pass the actual reductionH, localizationH, scalarRationalH and
scalarQbarH maps into CoefficientCompatibility. Its definition explicitly requires
IsIso of that exact argument, plus its own Frobenius intertwining square. No
quantification over arbitrary maps remains, and rank one alone cannot imply the
invertibility of these specified maps.

Read every normalization of the added helpers, including negative signed reduction
by evaluation, completed derived scalar extension by its counit, field tensor towers,
coefficient-size lifts, and the integral equality identification. Checked their
endpoints against the recorded functor signatures; the remaining compilation errors
were caused by forgetting the integral equality identification before H⁰ and by
leaving the ordinary tensor adjunction's module universe implicit. Both now appear
explicitly. The integral equality is a named postponed theorem; its def uses eqToIso,
so no arbitrary map is introduced. All other chosen comparisons are uniquely pinned
by their pure tensors or displayed hom formula, with proof docstrings explaining
existence and uniqueness.

Checked m=0, m=1, negative m=-d (including d=0), n+1=1, ramified E, l=2,
identity embeddings and arbitrary finite extensions, and independent Ω universe v.
Finite reduction uses the actual varpi_E quotient, not an l-power surrogate.
RationalF retains exactly the first component of globalGeometricFrobenius.
The common-stage endpoint transports are the recorded ones. The report now names
the canonical maps and explains each construction instead of defending the rejected
formulation. Every declaration is attached to the owning DAG node. No other node
field or target statement changed.

Final validation (2026-10-19 UTC): scompile.py passed both the sandbox module
(30.6 s) and its final library path (35.8 s), with no errors or warnings.
The server deliver2.py --no-push returned OK: preflight and per-file compilation
passed. Self-check found 51 attached declarations, an exact verbatim main signature,
no line over 100 characters, and no non-lean field changed against the current DAG.
