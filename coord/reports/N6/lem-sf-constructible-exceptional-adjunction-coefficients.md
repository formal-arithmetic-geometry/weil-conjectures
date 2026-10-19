## Worker report

Item: `lem-sf-constructible-exceptional-adjunction-coefficients`.
Module: `Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients`.
Main declaration: `WeilConjectures.ConstructibleExceptionalCoefficients.exists_system`.
All names below are in `WeilConjectures.ConstructibleExceptionalCoefficients` unless qualified.

The theorem asserts the existence of the full, normalized system of conclusions.
`RingSystem`, `FieldSystem`, `CommonSystem`, `RefinementSystem` and `System` are output records, not assumptions about geometric functors.
`System` contains one ring record, its field and common-stage records, and its refinement
record; each later record refers to the identical earlier data. Their fields spell out the functors, preservation, adjunctions, canonical-map
normalizations and coherence. `C` is an abbreviation for the published categories;
none of these categories, coefficient rings, localizations or comparison sites is copied.
There is no definition choosing a geometric operation from a bare `Nonempty` theorem.
The source characterizes the higher exceptional functors by the resulting adjunction;
the finite realization and all reduction, localization and common-stage comparisons
retain this characterization at the actual coefficient stages.

### Hypotheses

- `D : FiniteFieldDatum` supplies the global prime p, q, finite field and its algebraic
  closure k. `l`, `[Fact l.Prime]`, `hl : l ≠ D.p` are exactly the coefficient-prime data.
- `FieldStage.carrier`, its Field, Padic-algebra and FiniteDimensional instances package
  each finite E/Q_l. The integers, uniformizer and quotient rings are the existing
  `Padic.coefficientExtensionIntegers`, `coefficientExtensionUniformizer` and
  `coefficientExtensionRing`, as used by the dependency categories. Changing a uniformizer
  by a unit leaves each defining ideal unchanged; no additional uniformizer is assumed.
- `Ω`, its Field/Algebra instances and `IsAlgClosure (Padic l) Ω` give Qbar_l.
- `X.Over (Spec (.of D.k))` and the analogous Y instance give the structure maps.
  `LocallyOfFiniteType` plus `QuasiCompact` on each structure map is finite type.
- `f.IsOver`, `IsSeparated f`, `LocallyOfFiniteType f`, `QuasiCompact f` give precisely
  the separated finite-type k-morphism. The structure maps have no separatedness assumption.
  All these hypotheses appear explicitly in `exists_system`, `RingSystem` and `System`.

### Clause-by-clause rendering

| Node clause | Lean rendering |
| --- | --- |
| Ordinary constant finite coefficients, all positive levels | `Stage.finite E (n : ℕ+)`; `C` is `finiteTorConstructibleCategory`; `RingStage.coefficients` uses `PurCompactSupport.finite` |
| Completed derived-complete integral coefficients | `Stage.integral E`; `C` is `finiteTorConstructibleIntegralCategory`, including a single uniform Tor interval over every reduction |
| Raw E scalar localization | `Stage.rational E`; `C` is `sfRationalConstructibleCategory`; `rationalization` is the existing localization after the finite-Tor full inclusion |
| Common finite fields for Qbar | `Stage.closed`; `C` is `generalAlgebraicallyClosedConstructibleCategory`; `commonField` uses the existing small coefficient model |
| F and G preserve the finite-Tor domains | `Operation.F` and `.G` have those actual categories as source and target |
| Compact supports F | `RingSystem.left` realizes F as the actual proper/open `PurCompactSupport.image`; `integralLeft` and its normalization use the normalized strict-tower functor and `sfQcqsCompactSupportRealization`; `rationalLeft` uses the published raw Hom extension |
| Specified finite exceptional G | `RingSystem.finiteRight` identifies G with the actual intrinsic `ProEtale.sfFiniteExceptional`, the recorded module's fixed-scalar comparison composite in intrinsic coordinates |
| Exactness and shifts | `Operation.leftExact`, `.rightExact`, left/right Additive and CommShift fields; unitShift/counitShift; `Comparison.qShift`, `.bShift`; refinement shift fields |
| Natural Hom equivalence | `Operation.adjunction : F ⊣ G`; its `homEquiv` is natural in both variables by Mathlib's Adjunction laws |
| Units, counits and both triangles | `Operation.adjunction.unit`, `.counit` and the two triangle identities already in Adjunction; no separate weakened Hom assertion |
| Finite quotient A_m to A_n, 1 ≤ n ≤ m | `Allowed.quotient E m n h`, using `finiteQuotientChange` |
| Integral reduction R to A_n | `Allowed.reduction`, using the actual completion projection and derived extension; `finiteScalar_eq` and normalization fix the actual derived tensor restriction |
| Finite scalar extension retaining the base uniformizer | `Allowed.ramified`: Ramification, positive e and n, target level e*n; the map is `PurCompactSupport.finiteChange` |
| Any further quotient | `Allowed.comp` combines the ramified extension and a quotient, with actual coefficient maps required to compose; the quotient bound is 1 ≤ m ≤ e*n |
| Integral scalar extension | `Allowed.integral`, `integralScalar_eq` identifies the restricted functor with `integralScalarExtensionOfUniverses`; `integralScalar_normalized` fixes its realization by `completedScalarComparison`, the prescribed zero-shifted-coordinate quotient-cone map |
| Actual finite scalar functors | `Scalar.realization`, `finiteScalar_eq`, `finiteScalar_normalized`; scalar data is not an unconstrained extra functor |
| Canonical q | `Comparison.q`; `QNormalized` fixes it to `PurCompactSupport.comparison`, the normalized scalar-adjunction mate of the identity-on-sections restriction comparison |
| Canonical b | `Comparison.b` together with `.counit` characterizes b as the counit transpose of inverse q; b is an isomorphism, not just a transformation |
| Displayed unit equation | `Comparison.unit`: TX(eta) ≫ b(FK) ≫ G'(qK) = eta'(TXK) |
| Displayed counit equation | `Comparison.counit`: q(GL) ≫ F'(bL) ≫ epsilon'(TYL) = TY(epsilon L) |
| Identity and composition cocycles | `ScalarIdentity` and `ScalarComposition` are normalized by the actual tensor unit/associator; `RingSystem.identityLeft`, `.identityRight`, `.cocycle` give both q and b laws |
| Rationalization compatibility | `FieldSystem.rationalizationComparison` contains both equations; `.rationalization_normalized` fixes q using the actual integral action and raw localization |
| Rational scalar extension | `rationalScalar` is the published completed extension after localization; `rationalComparison` contains q/b and the equations; `rational_normalized` is the localized integral q on unchanged integral representatives |
| Rational identities/composition | `rationalCocycle`, `rationalIdentityLeft`, `rationalIdentityRight`, with the existing `sfRationalScalarComp` and `sfRationalScalarUnit` |
| Common-stage comparisons | `commonComparison`, `common_normalized` (identity on the literal finite-stage pair), and `commonCocycleLeft/Right`; `commonTransition` is transported from the specified stage-system transition by its defining equality |
| Compactification-refinement compatibility | `RefinementComparison.unit/counit`, `RingRefinementNormalized` fixes the proper/open comparison by open-unit and proper-counit equations; `refinementRational` and `refinementCommon` descend it; `refinementIdentity` and `refinementComposition` give coherence |
| Field reduction uses integral representatives | `rational_normalized` quantifies over K in the integral finite-Tor category before applying raw rationalization; no field-to-residue functor exists in this signature |
| No unrestricted ambient pro-etale adjoint | Only the constructible finite-Tor categories carry the asserted adjunction; the ambient G appears only as the prescribed finite comparison composite |

The helper records package this item's own conclusion. They are not independent notions
requiring a second definition node. `finiteTriangulated` projects the existing finite-Tor
triangulation theorem. `integralTriangulated` supplies the same elementary closure construction
on the intrinsic completed predicate needed to type this assertion: reductions are exact,
common interval bounds survive shifts/triangles, and derived completeness and bounded
constructibility have the published closure properties. Its docstring gives this full proof.
The main theorem docstring reproduces all thirteen DAG proof steps and their dependencies.

### Dependency declarations used

- `def-weil-finite-field-fiber`: `Sheaf.Paper.FiniteFieldFiber`, `WeilConjectures.FiniteFieldDatum`.
- `def-weil-l-adic-coefficient-extension`: `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`, `Padic.finite_coefficientExtensionRing`.
- `def-weil-scheme-morphism-properties`: `None`, `None`.
- `def-weil-pbc-proetale-modules`: `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`, `AlgebraicGeometry.ProEtale.FiniteCoefficientModules`.
- `def-weil-derived-complete-integral-detailed`: `Sheaf.Paper.SfIntegralConstructible`, `WeilConjectures.sfIntegralConstructible`.
- `def-weil-rationalization-karoubi`: `Sheaf.Paper.SfRationalizationKaroubi`, `WeilConjectures.sfRationalConstructibleCategory`.
- `def-weil-algebraically-closed-coefficients`: `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients`, `WeilConjectures.generalAlgebraicallyClosedConstructibleCategory`.
- `def-weil-finite-tor-amplitude`: `Sheaf.Paper.FiniteTorAmplitude`, `WeilConjectures.finiteTorConstructible`.
- `def-compact-support-direct-image-detailed`: `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriek`, `AlgebraicGeometry.ProEtale.rightDerivedLowerShriekOfCompactification`.
- `def-weil-integral-rational-qbar-compact-support`: `Sheaf.Paper.QcqsCompactSupportRealization`, `WeilConjectures.sfQcqsCompactSupportRealization`.
- `def-weil-exceptional-inverse-image`: `Sheaf.AlgebraicGeometry.FixedFiniteExceptionalAt`, `AlgebraicGeometry.ProEtale.sfFiniteExceptionalAt`.
- `def-weil-integral-derived-reduction`: `Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction`, `WeilConjectures.scalarReductionDerivedExtension`.
- `def-weil-integral-scalar-extension`: `Sheaf.Paper.IntegralScalarExtensionUniverses`, `WeilConjectures.integralScalarExtensionOfUniverses`.
- `lem-weil-finite-ctf-triangulated`: `Sheaf.Paper.FiniteCtfTriangulated`, `AlgebraicGeometry.Scheme.finite_ctf_isTriangulated`.

Additional canonical APIs reused (through the dependency modules) are
`PurCompactSupport.comparison`, `tensorComposition`, `tensorIdentity`,
`finiteTorIntegralInclusion`, `refinementRestriction`, `geometricPushComposition`,
`sfCompactSupportFiniteIntegralFunctor`, `sfCompactSupportFiniteFunctor`,
`sfQcqsCompactSupportRealization`, `completedScalarComparison`,
`sfRationalScalarComp`, `sfRationalScalarUnit`, and the existing common-stage inclusions,
transition equality and `StageSystem.transIso`.

The finite triangulation node was already landed; it is added to stmt_deps because the
statement's inherited category instances now use its declaration directly. No statement,
proof or proof-dependency field is changed. No statement correction or disputed claim arose.

### Edge cases and searches

- Empty schemes and zero objects: no nonemptiness or positive dimension assumption is
  introduced; inherited zero objects, exact functors and adjunction triangle laws apply.
- n=0 is excluded exactly by ℕ+; n=1, equal quotient levels and identity scalar extensions
  remain included. The quotients need not be flat: all finite changes are derived.
- e=1 and e>1 are both included. A target exponent beyond e*n cannot be supplied by the
  quotient constructor. Integral change is the completed construction even for identities.
- X and Y may be nonseparated over k; only f is separated. No affine/projective/proper
  assumption on f is added. Compactifications are universally quantified output indices.
- Rational categories keep integral objects and localized Homs, without Karoubi completion.
  Common-stage repeated fields and identity inclusions are retained by their cocycles.
- `autoImplicit false` and the explicit universe declaration rule out unintended free binders.
- LeanSearch query: “Constructible exceptional adjunction compact support coherent derived
  coefficient change”: 8 results, principally generic derived-adjunction lemmas; no match.
- LeanFinder query: “Constructible exceptional adjunction with compact support and coherent
  change of coefficients finite integral rational algebraically closed”: 8 unrelated
  condensed/module adjunction results; no match.
- Loogle `CategoryTheory.Adjunction`: 12 generic adjunction constructors and examples;
  reused Adjunction, no geometric all-coefficient theorem. Earlier `CategoryTheory.NatIso`
  query was not recognized, so it was replaced by this valid query.
- Mathlib grep `exceptional|constructible.*adjunction` under CategoryTheory: zero hits.
- rg/grep in upstream WeilConjectures and project Sheaf for the item id and
  exceptional/constructible adjunction and coefficient names found the recorded finite
  exceptional functor and `FiniteCoefficientAdjointComparisons`; the latter is a finite-stage
  separated-base interface, not this all-stage, nonseparated-base assertion.
- The upstream name index was searched for the item and new main names; no exact match.
  Raw search evidence is retained in `searches.jsonl`.

### Validation

All compilation uses the prescribed scompile.py wrapper, single files only. The full
proof-import audit exposed old and finite-coefficient upstream modules declaring identical
names. Following the launcher's duplicate-import repair rule, six incompatible proof-only
imports were omitted: CompactificationCoherence, PurityAffineChartBounds,
ProEtaleExtensionZeroComparison, EtaleCoefficientSystemAdjoint,
CanonicalCompactSupportSiteComparison, EtaleOriginAdjointClass. Their mathematical proof
steps remain in the docstring; the supported fixed/intrinsic modules supply every declaration
used by the statement, including the canonical proper/open refinement maps. No library file
was edited. Further compile/preflight results are appended below when complete.

## Second reading by N6

The dispatcher brief reserves independent review for the maintainer and forbids starting
another agent. No independent worker reading is claimed here. A fresh clause-by-clause
worker pass caught and repaired: arbitrary-scheme scalar quantification (now only X/Y),
missing actual completed-scalar identification (now integralScalar_eq plus normalized
completion map), missing finite tensor normalization (now finiteScalar_eq/normalized),
and an unspecified common-stage left comparison (now identity on literal pairs).
The report table and the node statement were read together with the final module.

Final scompile.py check: exit 0, no errors or warnings. Sandbox check 25.9 s;
actual module check 30.7 s, both below 60 s. No global build was run.

Delivery dry run passed: `deliver2.py ... --no-push` printed OK for commit
`37c2d78658`; maintainer preflight and both per-file compilation checks passed.

## Independent second reading (maintainer review service, 2026-10-18)

The section above is a self-check by the worker, as it says itself. This is the independent
clause-by-clause reading of the node against `exists_system` and its output records.

| Node clause | Lean | Verdict |
| --- | --- | --- |
| k = F_q-bar, char p; prime l ≠ p | `D : FiniteFieldDatum`, `[Fact l.Prime]`, `hl : l ≠ D.p` | same |
| finite E/Q_l, R = O_E, ϖ, A_n = R/ϖ^n, n ≥ 1 | `FieldStage` (field, Q_l-algebra, finite-dimensional); `Padic.coefficientExtension*`; `n : ℕ+` | same; n = 0 excluded as in the node |
| X, Y finite type over k, need not be separated | `X.Over`, `Y.Over`, LocallyOfFiniteType + QuasiCompact structure maps; no separatedness | same |
| f separated, finite type, over k | `f.IsOver`, `IsSeparated f`, `LocallyOfFiniteType f`, `QuasiCompact f` | same |
| C_{T,Λ} = D^b_ctf at A_n, R, E, Qbar_l | `C`: `finiteTorConstructibleCategory`, `finiteTorConstructibleIntegralCategory`, `sfRationalConstructibleCategory`, `generalAlgebraicallyClosedConstructibleCategory` | the recorded categories of the stmt_deps |
| F = Rf_! | `left` = `PurCompactSupport.image` (j_! then Rp_*), `integralLeft` + `sfQcqsCompactSupportRealization`, `rationalLeft` = `sfCompactSupportFiniteFunctor`, closed stage pinned by `common_normalized` | same object up to iso |
| G = Rf^! | `finiteRight` identifies G with `ProEtale.sfFiniteExceptional` (the intrinsic interface re-exported by the recorded module FixedFiniteExceptionalAt); higher G determined by the adjunction | same; no ambient adjoint |
| preservation, exactness, adjunction, naturality, triangles | `Operation` (functors between the ctf categories, `F ⊣ G`, IsTriangulated, CommShift, unit/counit CommShift) | same |
| refinement comparisons | `RefinementSystem`, `RingRefinementNormalized` (open unit, proper counit), identity/composition | same |
| coefficient changes: quotient, reduction, ramified finite (en), further quotient, integral ext., rationalization, rational ext. | `Allowed.quotient/reduction/ramified/integral/comp/identity`, `rationalization`, `rationalScalar` | same; `Ramification` pins e |
| q, b isomorphisms; unit and counit displays | `Comparison.q/b` (≅), `.unit`, `.counit`, written in diagrammatic order | same equations |
| q canonical | `QNormalized` (mate `PurCompactSupport.comparison`), `rationalization_normalized`, `rational_normalized`, `common_normalized` | canonical, not arbitrary |
| identity/composition cocycles, shifts, common stage | `scalarIdentity`, `identityLeft/Right`, `cocycle`, `rationalCocycle`, `rationalIdentity*`, `commonCocycleLeft/Right`, `qShift/bShift` | same |
| field reduction through integral representatives | `rational_normalized` quantifies over integral K | same |

Edge cases: empty X or Y (no nonemptiness assumption); n = 1, m = n, e = 1, identity
extensions (Allowed.identity) are all included; nonseparated X, Y; universes are one u with no
equality forced beyond the one the recorded coefficient categories already have.

Changes made by the reviewer: the docstring of the helper `integralTriangulated` now names its
DAG statement lem-weil-integral-ctf-triangulated (stated on the def-weil-finite-tor-amplitude
predicate) and Stacks 08G2. Nothing else was changed. Compile check of the fixed file with
nt_compile.py: exit 0, 21.7 s.
