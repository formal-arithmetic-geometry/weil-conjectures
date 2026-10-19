## Worker report

Item: `lem-coef-integral-compact-support`, group Q131, stage 2, 2026-10-17.
Retained the previous attempt's module and repaired its compiler diagnostics; the saved
packet had no report and no Lean record. No mathematical node field has changed.
The module is `Sheaf.Paper.IntegralCompactSupportPrescribedReductions` and the main
statement is `WeilConjectures.integralCompactSupport_prescribedReductions`.
Its only postponed theorem has proof `by sorry`; its docstring contains all nine DAG
proof steps. The three helpers supply a product instance, the actual finite transition,
and the canonical coefficient map, with real data and source/blueprint docstrings.

Read the current node and each statement dependency's statement and recorded Lean
interface. The current blueprint text is
`literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-lem-sp-tower/lem-coef-integral-compact-support.md`
and its separate `.proof.md`; it has the same mathematical statement and two proof
paragraphs as the archived source at blueprint order 2135 named by the DAG.

Hypothesis-by-hypothesis correspondence:

- Global finite-field datum: `(D : FiniteFieldDatum.{u})` supplies `p`, `q`, the
  finite base field and its fixed algebraic closure `D.k`. Prime coefficient `l` is
  bound with `[Fact l.Prime]`; `_hl : l ≠ D.p` is exactly the excluded characteristic.
- Finite extension of Q_l: `(E : Type u) [Field E] [Algebra ℚ_[l] E]
  [FiniteDimensional ℚ_[l] E]`. The dependency's chosen integer ring, uniformizer,
  quotient and quotient maps are used via `Padic.coefficientExtensionRing` and
  `Padic.coefficientExtensionTransition`; no second coefficient system is defined.
- Integral coefficients: `DerivedCategory (scalarReductionSource.{u, u} l E X)`
  and the analogous category on Y are modules over the dependency's completed ring
  sheaf, not the discrete constant sheaf of E's integers.
- Finite-type k-schemes: `X Y : Scheme.{u}`, the two `Over (Spec (.of D.k))`
  instances and `LocallyOfFiniteType` plus `QuasiCompact` on both structure maps.
  No separatedness of those structure maps is imposed.
- Separated finite-type k-morphism: `{f : X ⟶ Y}`, `[f.IsOver (Spec (.of D.k))]`,
  `[IsSeparated f]`, `[LocallyOfFiniteType f]` and `[QuasiCompact f]`.
- The fixed compactification from the compact-support definition is
  `(c : Compactification f)`, identical at every coefficient level. This unpacks
  the choice in the recorded definition, rather than imposing properness on f.
- Nonnegative integer dimension bound: `(d : ℕ)` and
  `_hd : topologicalKrullDim X ≤ (d : WithBot ℕ∞)`. Naturals represent precisely the
  permitted nonnegative integers, including zero.
- Ordered input interval: `(a b : ℤ)` and `_hab : a ≤ b`.
- Input integral constructibility: `(K : DerivedCategory (scalarReductionSource ...))`
  and `_hK : sfIntegralConstructible l E X K` use the recorded dependency unchanged.
- The common reduction Tor interval is `_hTor : ∀ n : ℕ,
  HasProEtaleTorAmplitude X (Padic.coefficientExtensionRing l E (n + 1))
  ((scalarReductionDerivedExtension ... X n).obj K) a b`.
  This is the intrinsic all-module test used inside the recorded finite-Tor predicate,
  not Tor amplitude of geometric stalks or merely cohomological boundedness.
- `M`, `p`, `δ` and `_hc : IsDerivedLimitTriangle
  (sfCompactSupportTransition l E c K) M p δ` specify the defining Rlim and its
  projections. They are the data of Rf_!K itself. The theorem quantifies over its
  realizations so the chosen value of `sfIntegralCompactSupportValue` is covered.
  There is no extra existence assumption on K: `coefCompactSupportHasProduct` obtains
  the product from the published `integralOperationsDerivedCountableProducts`, and
  `exists_isDerivedLimit_and_iso` supplies these Roos triangles. The projection must
  be retained to state the canonical map; an arbitrary isomorphism is insufficient.

Conclusion-by-conclusion correspondence:

- `Rf_!K ∈ Dᵇ_c(Y,R)` is `sfIntegralConstructible l E Y M`.
- The displayed canonical map at every positive level is
  `coefIntegralCompactSupportComparison l E c K M p n`. Its definition is exactly
  `((derivedScalarExtensionRestrictionAdjunction ...).choose.homEquiv M _).symm
  (p ≫ Pi.π _ n)`, the normalized tensor/restriction adjunct of the n-th projection.
  Its target is the existing finite compact-support candidate applied to the existing
  derived reduction of K. The second conjunct asserts `IsIso` of this specified map.
- The output reduction Tor interval is the third conjunct, the same intrinsic
  `HasProEtaleTorAmplitude` predicate on the reduction of M, with endpoints
  `a` and `b + 2 * (d : ℤ)`. Its isomorphism to the finite compact-support value gives
  that value the same interval too, so both displayed readings are covered.
- Compatibility with successive reductions is the final conjunct. At n+1 then n,
  the coefficient comparison followed by `coefCompactSupportFiniteTransition` equals
  the actual output reduction transition followed by derived restriction of the n-th
  comparison. The finite transition is the exact expression already inside
  `sfCompactSupportTransition`, before restriction to completed coefficients: apply
  the higher compact-support functor to the actual input reduction map, then apply
  `sfCompactSupportRestriction`. Adjacent compatibilities compose, giving every
  successive quotient reduction; no unrelated isomorphisms are selected.

Dependency declarations used (namespace `WeilConjectures` unless stated otherwise):

- `Sheaf.Paper.FiniteFieldFiber`: `FiniteFieldDatum`.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`: `Padic.finite_coefficientExtensionRing`,
  importing the integer ring, uniformizer, quotient rings and their transitions.
- `Sheaf.Paper.CompletedIntegralCoefficientGerm`: `integralConstantToCompletion`,
  importing `completedIntegralCommRingSheafUnrestricted` and its actual projections.
  The extra stalk action is not needed here; the same completion is used.
- `Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction`:
  `scalarReductionSource`, `scalarReductionDerivedExtension`,
  `scalarReductionDerivedRestriction`, `derivedScalarExtensionRestrictionAdjunction`.
- `Sheaf.Paper.SfIntegralConstructible`: `sfIntegralConstructible`.
- `Sheaf.Paper.FiniteTorAmplitudeProEtaleModule`: the recorded finite-Tor interface;
  its public dependency `Sheaf.Paper.FiniteTorAmplitude` defines
  `finiteTorConstructibleIntegral` using the very same uniform reduction test.
  The specified interval uses `AlgebraicGeometry.Scheme.HasProEtaleTorAmplitude`
  from `Sheaf.AlgebraicGeometry.ProEtaleTorAmplitude`.
- `WeilConjectures.Mathlib.Topology.KrullDimension`: `topologicalKrullDimAt` and the
  imported Mathlib `topologicalKrullDim` on the underlying scheme space.
- `Sheaf.Paper.IntegralRationalQbarCompactSupport`: `sfIntegralCompactSupportValue`
  and the publicly imported `sfCompactSupportTerm`, `sfCompactSupportTransition`,
  `sfCompactSupportReductionTransition`, `sfCompactSupportFiniteRestriction`.
- `Sheaf.Paper.SfCompactSupportRestrictionOfScalars`:
  `AlgebraicGeometry.Scheme.sfCompactSupportRestriction` and the finite candidate.
- The morphism-properties dependency is an aggregator, with no definition to copy:
  the statement uses Mathlib `LocallyOfFiniteType`, `QuasiCompact`, `IsSeparated`.

Edge cases checked: the empty scheme is permitted (Krull dimension bottom is ≤ d),
d=0 is permitted, a=b and zero K are permitted, and no nonempty/proper/smooth
hypothesis is added. Natural index zero denotes exponent one, so the residue quotient
is included and exponent zero is correctly excluded. All positive exponents occur.
The coefficient characteristic restriction is exactly l≠p. The small pro-etale site
keeps its existing object universe u+1 and morphism universe u; no equality of these
universes is imposed. Every binder and universe is explicit (`autoImplicit false`).

Searches retained from `searches.jsonl` of the earlier attempt (2026-10-17):

- msearch loogle: `WeilConjectures.sfIntegralCompactSupportValue, IsIso` — unknown
  project identifier in the Mathlib service, no match.
- msearch leanfinder: `Integral compact support preserves constructibility and derived
  reduction with uniform Tor amplitude` — eight hits, all unrelated analytical compact
  support or constructible images of scheme morphisms, no match.
- msearch grep: `compactSupport.*(reduction|[Cc]oefficient)|[Ii]ntegral.*[Cc]ompact.*[Ss]upport`
  — 25 unrelated analytical integration/convolution hits, no match.
- msearch leansearch: `Integral compact support derived coefficient comparison Tor amplitude`
  — eight unrelated analytical compact-support and t-structure hits, no match.
- Source/project rg for `HasProEtaleTorAmplitude`, `sfCompactSupportTerm`,
  `derivedScalarExtensionRestrictionAdjunction`, `IsDerivedLimitTriangle` found the
  dependency interfaces used above. `sfIntegralCompactSupport_constructible` states
  integral membership only, without the prescribed comparison or quantitative Tor bound.
- Source/project/Mathlib rg for `integralCompactSupport_prescribedReductions`,
  `coefIntegralCompactSupportComparison`, `coefCompactSupportHasProduct` returned no
  existing declaration. Upstream grep for this blueprint id returned no hit.

Validation: scompile.py compiled this module individually, both as sandbox and under
its delivered module path, without warnings or errors. The initial missing Tor import
was repaired. The product is supplied from the dependency's existing construction,
without adding a hypothesis. No new node or dependency replacement is needed.

Import fault reported for maintainer review: two proof-only modules cannot presently
join this finite-coefficient import closure. `Sheaf.Paper.CompactificationCoherence`
fails while importing `RefinementComparisonIsomorphism`; the compiler reports a
collision on `AlgebraicGeometry.ProEtale.upperStarIsoLowerStarInv` between
`WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.Iso` and
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Iso`.
`Sheaf.Paper.EtaleCompactSupportCoefficientChange` reaches the same collision through
`CompactSupportCoefficientChange` → `CompactSupportRestrictionOfScalars` →
`ProEtaleFixedScalarRestrictionDirectImage` → the old derived restriction module.
The delivered module retains the finite-coefficient side and omits these two
proof-only imports; all other recorded proof dependencies are imported. Neither
missing import supplies an object in this theorem's signature. Their mathematical
uses remain in the nine-step proof docstring and in unchanged proof_deps.

## Second reading by Q131

Dispatcher-mode self-check, performed with the node, source blueprint, dependency
interfaces and module open; no separate worker is claimed (the dispatch brief forbids
starting other agents). The maintainer performs the independent delivery review.
Matched each hypothesis and conclusion as above. Found and repaired the saved file's
missing intrinsic-Tor import and missing product interface, without adding a product
hypothesis. Checked the projection adjunct direction, the finite restriction direction
(lower-level modules to higher-level modules), and both sides of the successive-reduction
square. The output bound is b+2d, with d cast to integers. The main theorem remains
sorry-only; helper definitions do not select arbitrary coefficient maps. The node's
statement is unchanged, and its Lean signature is copied verbatim from the file.
