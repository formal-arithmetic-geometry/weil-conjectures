## Worker report

The module `Sheaf.Paper.ConstantCoefficientObjectsConstructible` states all three parts
of `lem-weil-constant-coefficient-objects-constructible`. The node is unchanged except
for `lean`. There are no new nodes or dependency repairs in this delivery. Every theorem
has `sorry` as its entire proof; every helper definition has actual data. The primary
recorded declaration is `WeilConjectures.integralConstantCoefficient_constructible`,
with all twelve declarations listed in `lean.declarations`.

Sources read: the item's complete DAG statement and ten proof steps; the blueprint
`sec-smooth-purity/sk-def-sf-admissible/def-weil-ordinary-compact-cohomology.md`,
order 1510; Bhatt--Scholze, Definition 6.8.1 and Lemma 6.8.2, printed pp. 58–59.
The latter identify the integral coefficient sheaf with the inverse limit of finite
constant coefficient sheaves, for an arbitrary scheme. The proof plans in this module
also retain the node's Sections 3.5 and 6.5 arguments. The item is not the blueprint
unit's statement, and no statement correction is required.

Hypotheses and objects:

- The global datum `(p,a,q,k₀,k)` is the recorded `FiniteFieldDatum.{d}`. All rational
  objects and stage-independence statements use `(D : FiniteFieldDatum.{d})`,
  `(l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)`.
- The fixed algebraic closure is `(Ω : Type v) [Field Ω] [Algebra (Padic l) Ω]
  [IsAlgClosure (Padic l) Ω]` in the common-stage construction. Its universe is
  independent of the scheme universe. Finite coefficient fields inside it are
  `AlgebraicallyClosedCoefficients.Index l Ω`; their actual small field models are
  the dependency's `Coefficient.{u} l Ω E`, never a replacement stage category.
- Outside the pair construction, `(E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E]` renders a finite coefficient extension. The same
  binders for `L` and `(ι : E →ₐ[Padic l] L)` render a finite extension inclusion.
  An algebra homomorphism of these fields is injective. These helper statements do
  not need a choice of closure: applying them to the recorded `Coefficient` models
  gives precisely the finite subextensions in the fixed closure in the node.
- The valuation ring, uniformizer, and finite quotient are exactly
  `Padic.coefficientExtensionIntegers`, `Padic.coefficientExtensionUniformizer`, and
  `Padic.coefficientExtensionRing`. There is no independent uniformizer or ring.
- `(Y : AlgebraicGeometry.Scheme.{u})` has no finiteness, separation, or base-field
  restriction, as required by the item. The small site remains `ProEt.topology Y`
  (objects in `u+1`, morphisms in `u`), not a site with those universes identified.
- Every `(n : ℕ)` in this file denotes the positive exponent `n+1`. It includes every
  `n≥1` in the node and excludes no positive level. There is no quotient at exponent
  zero in the statement.

Clause-by-clause rendering:

1. `finiteConstantCoefficientObject l E Y n` is
   `(DerivedCategory.singleFunctor _ 0).obj (SheafOfModules.unit
   (integralCoefficientSheaf l E Y n))`. Mathlib's `unit` is the actual regular module
   of the recorded constant ring sheaf, and `singleFunctor ... 0` places it in degree
   zero. No arbitrary coefficient object is supplied as an assumption.
   `finiteConstantCoefficient_constructible` states its membership in
   `intrinsicFiniteTorsionConstructible l E (n+1) ... Y`. Its next conjunct is
   `IsLocallyConstantProEtaleModuleSheaf Y ...` for that same sheaf, expressing the
   single stratum Y. Its last conjunct quantifies over every geometric point, gives
   an additive equivalence from the coefficient ring (with its required ULift) to
   the actual geometric module stalk, requires compatibility with multiplication
   through `proEtaleConstantRingGerm`, and explicitly asserts that stalk is finite.
   Thus the identification retains the coefficient-module action.
2. `integralConstantCoefficientObject` is the completed ring's regular module in
   degree zero. `integralConstantCoefficient_constructible` states its membership
   in the original `boundedConstructibleDerivedCompleteIntegral` used by the
   published rationalization AND in the current recorded `sfIntegralConstructible`
   interface. These are two encodings of the same clause, not two different
   constructions of coefficients. Their predicates include derived completeness,
   all positive constructible reductions, and uniform finite amplitude. The next
   conjunct explicitly uses the currently recorded `IsDerivedCompleteUnrestricted`.
   For each level the theorem asserts `IsIso (constantCoefficientReductionMap ...)`
   and `proEtaleCohomologicalSupport ... ⊆ Set.Icc 0 0` for the actual recorded
   `scalarReductionDerivedExtension`.
   The reduction morphism is constructed, rather than existentially supplied:
   `constantCoefficientProjection` is the unique regular-module map sending 1 to
   the compatible section 1 of the restricted quotient sheaf. Linearity makes its
   value on x precisely π_n(x). Place this map in degree zero, use Mathlib's
   `mapDerivedCategorySingleFunctor` comparison for exact restriction, and transpose
   through the dependency's normalized `derivedScalarExtensionRestrictionAdjunction`.
   This is the canonical map in the node. Its definition assumes no invertibility.
3. `constructibleIntegralConstantCoefficient` packages that explicit integral
   complex with the membership proof of Part 2. Its data do not depend on a sorry
   existence theorem; only its property proof is postponed.
   `rationalConstantCoefficientObject` is its image under the recorded
   `rationalConstructibleLocalization`, and so is E_Y in the raw rationalization.
   `AlgebraicallyClosedCoefficients.constantCoefficientPair` is the literal pair
   `⟨E, rationalConstantCoefficientObject ...⟩` in the recorded `Pair` category.
   `integralConstantCoefficient_scalarExtension` states the integral isomorphism
   under exactly `integralScalarExtension l E L ι Y`.
   `rationalConstantCoefficient_scalarExtension` states the resulting isomorphism
   under exactly `rationalScalarExtension D l hl E Y L ι`.
   Finally `constantCoefficientPair_stageIndependent` quantifies over every
   inclusion `h : E ≤ L` of finite fields inside the fixed closure. It supplies
   the rational coefficient isomorphism for the actual `stageTransition` and
   asserts `IsIso` of its actual `ofHom` class represented at L. Explicitly its
   representative is the inverse associator from T_(E,L) to T_(L,L)T_(E,L), followed
   by T_(L,L)(φ). This has source T_(E,L)(E_Y) and target T_(L,L)(L_Y), exactly the
   source and target required by the pair-category Hom formula. It is equivalent
   to the node's self-extension normalization ψ⁻¹φ. No bare nonempty isomorphism
   of unrelated pair objects replaces this class.

Dependency declarations read and used (all modules below are public imports when
listed among the node's statement dependencies):

| Dependency module | Declarations/interface used |
| --- | --- |
| `Sheaf.Paper.FiniteFieldFiber` | `WeilConjectures.FiniteFieldDatum` |
| `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` | `Padic.finite_coefficientExtensionRing`; publicly imports the original coefficient ring, uniformizer, integer-ring and transition constructions |
| `Mathlib.FieldTheory.IsAlgClosed.Basic` / `AlgebraicClosure` | `IsAlgClosure`, `IsAlgClosed`, `AlgebraicClosure` (through the recorded global-datum import) |
| `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory` | `AlgebraicGeometry.Scheme.proEtaleDerivedCategory` (publicly imported by the recorded dependencies) |
| `Sheaf.Paper.CompletedIntegralCoefficientGerm` | existing completion, finite ring sheaves and commutative versions, `integralConstantToCompletion` and constant germ interfaces; the completion used is `completedIntegralCoefficientSheafUnrestricted` |
| `Sheaf.Paper.IntrinsicFiniteTorsionConstructibility` | `intrinsicFiniteTorsionConstructible` |
| `Sheaf.Paper.SfIntegralConstructible` | current recorded `sfIntegralConstructible`, including its actual reductions and canonical completeness units |
| `Sheaf.Paper.DerivedCompleteUnrestricted` | current recorded `IsDerivedCompleteUnrestricted` |
| `Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction` | current recorded `scalarReductionDerivedExtension`, `scalarReductionRestriction`, normalized `derivedScalarExtensionRestrictionAdjunction` |
| `Sheaf.AlgebraicGeometry.ProEtaleCohomologicalSupport` | `proEtaleCohomologicalSupport` |
| `Sheaf.Paper.RationalizationKaroubi` | `rationalConstructibleCategory`, `rationalConstructibleLocalization`, `rationalScalarExtension`; its existing original integral predicate is retained for constructing its actual objects |
| `Sheaf.Paper.IntegralScalarExtension` | `integralScalarExtension` |
| `Sheaf.Paper.AlgebraicallyClosedCoefficients` | `Index`, `Coefficient`, `Pair`, `stageTransition`, `stageSystem`, `ofHom` |

The live records have several equivalent presentations from earlier bottom-up repairs.
They are imported as published; this delivery does not repair or restate those nodes.
`SheafOfModules.unit`, `unitHomEquiv`, `PresheafOfModules.sectionsMk`,
`DerivedCategory.singleFunctor`, and `Functor.mapDerivedCategorySingleFunctor` were
read in Mathlib and used directly. The actual upstream
`WeilConjectures.CategoryTheory.StageSystem.Basic` was read using `scompile.py --source`,
including `PairCategory`, `toStage`, `mkHom`, the associator, and representative composition.

All recorded proof dependencies with published modules are imported, including constant
stalks, the current constructibility and local-constancy interfaces, module stalks,
tensor product in independent universes, the surjective tower theorem, inverse limits,
and derived limits. The scheme-morphism-properties node has no recorded module and so
has no module to import. Its role (Y is constructible in itself) is included explicitly
in the finite theorem's proof plan. No imported proof module introduces a cycle.

Edge cases checked before and during writing:

- Empty Y: a single empty stratum is permitted; geometric stalk statements are
  vacuous, and cohomological support is contained in [0,0], rather than asserted
  equal to {0}. All coefficient objects can be zero.
- The least level is exponent one, obtained at n=0; every positive level occurs.
- E=L and the identity inclusion are included by the unrestricted `ι` and by
  `h : E ≤ L` (no strict inequality). Self-transitions are explicitly retained
  in the representative of the pair-category morphism.
- Ramified inclusions are not excluded; integral extension uses the recorded
  strict tower, not an assumed equality of uniformizers or ramification index one.
- No invertibility of l on Y is assumed. The scheme is arbitrary.
- The global-datum, closure, and scheme universes are independent. Small finite
  coefficient models are exactly the dependency's Shrink models, preserving all
  stages without a closure/site universe equality.
- The completion is the inverse limit of finite constant sheaves, never the discrete
  constant sheaf of O_E. Completeness asks for the canonical Roos triangle, not
  uniqueness of a freely chosen lift to a triangulated derived limit.

Searches for reuse (the msearch outputs are also in `searches.jsonl`):

- `msearch.py ... leansearch "A constant finite module sheaf is bounded constructible
  on the pro-etale site"`: eight hits, including `CategoryTheory.Sheaf.IsConstant`,
  `SheafOfModules.IsFiniteType`; no match to these coefficient categories or theorem.
- `msearch.py ... leanfinder "The constant finite torsion coefficient sheaf and completed
  integral coefficient sheaf are bounded constructible derived objects on the pro-etale
  site"`: eight unrelated completion/condensed hits (`BDeRhamPlus`, `BDeRham`,
  `Condensed.profiniteSolid`, etc.); no match.
- `msearch.py ... loogle "SheafOfModules.unit, DerivedCategory.singleFunctor,
  IsDerivedComplete"`: no hits; the external Mathlib index does not know the project's
  `IsDerivedComplete` identifier. Direct source inspection resolves all three interfaces.
- `msearch.py ... grep "constant.*constructible|unit.*[Mm]odule|def unit"
  Algebra/Category/ModuleCat/Sheaf`: one `unitToPushforwardObjUnit` hit in
  `PullbackFree.lean`, not the theorem. Direct Mathlib searches located the existing
  regular module `SheafOfModules.unit`, the single functor and exact functor comparison.
- `rg -n "constant.*[Cc]onstructible|[Cc]onstructible.*constant|constantCoefficient|
  constant_coefficient"` over the source project's `WeilConjectures` and side `lean/Sheaf`
  located the completed rings, constancy/stalk interfaces used here and the upstream
  etale `isConstructibleSheaf_unit`. Its full signature uses `X.smallEtaleTopology`
  and `Sheaf ... (ModuleCat ...)`, so it does not state the present pro-etale derived,
  completed integral, rationalized, and common-stage claims.
- `grep -rn "lem-weil-constant-coefficient-objects-constructible"` over the upstream
  source: no declaration attached to this node.
- Exact proposed declaration-name searches in Mathlib/project/side sources and
  `dag/lean_names_upstream.json`: no collisions. The side pro-etale module-object
  framework and `coord/pefw-upstream-framework.md` were read; its constructibility
  predicates concern internal module objects, not this recorded intrinsic completion
  and raw pair-category theorem. No parallel definition was introduced.

No STATEMENT-DISPUTED flag and no node fault. In particular, the source supports the
claim for arbitrary schemes; its finite-type restrictions on the later cohomology
application are not added to this coefficient-object lemma.


## Second reading by Q26

Independent review of the complete DAG node, its ten proof steps, the delivered
Lean module, and the dependency declarations. Verdict: the Lean renders all three
parts of the node. No statement correction, new node, dependency repair, or change
to the Lean module is needed. This reading changes only this report.

Source check: I read the blueprint definition
`sec-smooth-purity/sk-def-sf-admissible/def-weil-ordinary-compact-cohomology.md`
(order 1510), and the actual Bhatt--Scholze PDF, Definition 3.5.2 (printed p. 24),
the setup and Definition 6.5.1/Lemma 6.5.4 (p. 49), and the setup, Definition
6.8.1 and Lemma 6.8.2 with its proof (pp. 58--59). Section 6.5 begins with a
qcqs scheme; Section 6.8 explicitly begins with any scheme, and its finite-E
completion identity has no qcqs hypothesis. The present node's coefficient-object
claim, with its direct single-stratum/K-flat/replete-tower proof, is for arbitrary
Y. The separated finite-type k-scheme assumptions in order 1510 belong to the
cohomology application, not to this internal coefficient lemma. The Lean correctly
adds neither those hypotheses nor invertibility of l on Y. This node's source is
this blueprint and PDF, rather than a Stacks theorem with ambient hypotheses.

The following is my object/hypothesis/conclusion inventory and its comparison.

| Node item | Lean rendering and verdict |
| --- | --- |
| Fixed p,a,q,k0,k | `D : FiniteFieldDatum.{d}` in the integral membership, rationalization and pair statements. I read its structure: primality, positive exponent, q=p^a, cardinality of k0, and the fixed algebraic closure are present. Pass. |
| Prime l different from p | `[Fact l.Prime]` and `hl : l ≠ D.p`. The finite object and scalar-extension helper statements omit the irrelevant global datum, so specialize immediately to the fixed datum; they assume no additional property. Pass. |
| Fixed algebraic closure of Q_l | `(Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]` in the pair construction. `IsAlgClosure` is the Mathlib algebraic-closure predicate. Pass. |
| Finite E/Q_l in that closure | Helpers use `(E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]`. In the actual pair, `E : Index l Ω` is the finite intermediate field and `Coefficient.{u} l Ω E` is its existing Shrink model. I read `coefficientSmall`, `Coefficient`, `coefficientFinite`, and `coefficientInclusion`; this is the same finite field via its algebra equivalence, without identifying v and u. Pass. |
| O_E, chosen uniformizer, A_(E,n) | Existing `Padic.coefficientExtensionIntegers`, `coefficientExtensionUniformizer`, and `coefficientExtensionRing`. I read their definitions in `CoefficientExtension.lean` and the positive-level finiteness theorem. No independent coefficient ring or uniformizer is supplied. Pass. |
| Positive integer level | `(n : ℕ)` denotes exponent `n+1` everywhere, with the actual proof `Nat.succ_le_succ (Nat.zero_le n)` when the intrinsic predicate requires positivity. This enumerates exactly every n>=1 in the node. Pass. |
| Arbitrary scheme and its small pro-etale site | `(Y : AlgebraicGeometry.Scheme.{u})`; the imported constructions use `ProEt.topology Y`, not the etale site. I read `proEtaleDerivedCategory`, whose site object and morphism universes remain u+1 and u. Pass. |
| Finite constant sheaf, not constant presheaf | `integralCoefficientSheaf l E Y n` is the existing sheafification of the constant CommRingCat presheaf, forgetting commutativity afterward. Its `ULift` changes size only. Pass. |
| Completed integral coefficient sheaf | `completedIntegralCoefficientSheafUnrestricted` is literally `limit (integralCoefficientSheafSystem ...)`, with the recorded quotient reductions. It is not the discrete constant sheaf of O_E. Pass. |
| Part 1: finite object in degree zero | `finiteConstantCoefficientObject` is `DerivedCategory.singleFunctor _ 0` applied to `SheafOfModules.unit` of that constant ring sheaf. Mathlib's `unit` is the actual regular module, not an arbitrary object. Pass. |
| Part 1: membership in D^b_c(Y,A_(E,n)) | The first conjunct of `finiteConstantCoefficient_constructible` is exactly `intrinsicFiniteTorsionConstructible` of that object. I unfolded the dependency: finite cohomological support and constructibility of every cohomology sheaf in the same module category. Pass. |
| Part 1: locally constant on the one stratum Y | The next conjunct is `IsLocallyConstantProEtaleModuleSheaf Y ...` of the same regular module, on Y itself. I read its actual ringed-site definition, including the sheafified constant module and linear isomorphism over the localized coefficient ring. No stratum is substituted for Y. Pass. |
| Part 1: finite stalks equal to A_(E,n) | The last conjunct quantifies over all geometric points in the recorded small-site size convention and asserts an additive equivalence from the lifted ring to `proEtaleGeometricModuleStalk`, with `e (a*b) = proEtaleConstantRingGerm ... a • e b`, and actual `Finite` of that stalk. This is an isomorphism of coefficient modules, rather than a cardinality or additive-group-only assertion. Pass. |
| Part 2: completion placed in degree zero | `integralConstantCoefficientObject` is `singleFunctor _ 0` of the completed ring's actual regular module in `DerivedCategory (scalarReductionSource ...)`. Pass. |
| Part 2: membership in D^b_c(Y,O_E) | `integralConstantCoefficient_constructible` states `sfIntegralConstructible` of that object, the dependency's currently recorded predicate. It also states the original `boundedConstructibleDerivedCompleteIntegral` membership needed by the published rationalization. I read both definitions: each means completeness, all positive constructible reductions, and one uniform finite interval. These two presentations add no geometric or coefficient hypothesis. Pass. |
| Part 2: derived completeness | Explicit `IsDerivedCompleteUnrestricted` of the same object, in addition to completeness in each integral membership predicate. I read this declaration, `IsSfDerivedComplete`, and the existing integral predicate: they ask for the actual reduction units in a Roos triangle, not an arbitrary comparison with some object named completion. Pass. |
| Part 2: canonical reduction arrow | `constantCoefficientProjection` uses Mathlib's `unitHomEquiv` to send 1 to the compatible quotient section 1. Linearity then sends every section x to its image under the actual limit projection used by `scalarReductionRestriction`. `constantCoefficientReductionMap` places that map in degree zero, uses the exact-restriction single-functor comparison, and transposes it through `derivedScalarExtensionRestrictionAdjunction`. I read the adjunction's K-flat unit normalization. Thus this is the specified canonical reduction map, not an assumed or arbitrarily chosen morphism. Pass. |
| Part 2: reduction isomorphism at every level | `∀ n : ℕ, IsIso (constantCoefficientReductionMap l E Y n)`. Its source is the recorded `scalarReductionDerivedExtension` applied to the integral object, and its target is exactly the finite object of Part 1. Pass. |
| Part 2: common support interval [0,0] | In the same universal quantifier, `proEtaleCohomologicalSupport ((scalarReductionDerivedExtension ...).obj ...) ⊆ Set.Icc 0 0`. I read the support declaration: the set of integer degrees with nonzero cohomology. Pass. |
| Part 3: actual rational object E_Y | `constructibleIntegralConstantCoefficient` packages the explicit integral object using its membership theorem; `rationalConstantCoefficientObject` applies the recorded `rationalConstructibleLocalization`. The data is fixed before its membership proof; it is not chosen from an existence theorem. I read the raw localization definition, which adjoins no idempotents. Pass. |
| Part 3: actual algebraically closed object | `constantCoefficientPair` is literally `⟨E, rationalConstantCoefficientObject ...⟩` in the recorded `Pair`, not an isomorphic replacement category. Pass. |
| Part 3: finite inclusions E subset L | `(L : Type u)` with the same finite-dimensional field instances and `(ι : E →ₐ[Padic l] L)` in the helper theorems; actual inclusions of finite intermediate fields are `h : E ≤ L` in the pair theorem, via the recorded small-model inclusion. AlgHom of fields is injective. Pass. |
| Part 3: integral scalar extension isomorphism | `integralConstantCoefficient_scalarExtension` states `Nonempty` of the exact isomorphism between `(integralScalarExtension l E L ι Y).obj` of the integral object and the integral L-object. I read the published functor: its good-complex localization is the specified strict quotient/Roos construction. Pass. |
| Part 3: rational scalar extension isomorphism | `rationalConstantCoefficient_scalarExtension` states the analogous `Nonempty` isomorphism for the existing `rationalScalarExtension`. Its published object formula is the constructible completed integral extension followed by raw rationalization. Pass. |
| Part 3: its common-stage class is invertible | `constantCoefficientPair_stageIndependent` quantifies over every E,L,h, supplies an isomorphism φ for the actual `stageTransition`, and states `IsIso` of the actual `ofHom` representative at L. The representative is `assoc(h,refl).inv` followed by `T_(L,L).map φ.hom`; it has source `T_(E,L)(E_Y)` and target `T_(L,L)(L_Y)`, exactly the pair Hom formula. I read `stageSystem_existsUnique`, `stageTransition`, `Pair`, `StageHom`, `ofHom`, and fetched current upstream `StageSystem.Basic` with `scompile.py --source`. Its `isoToStage` and stage inclusion give precisely this associator/self-transition normalization. This class is the stage transport followed by the image of φ, so it is the node's induced class. Pass. |

The five statement docstrings collectively carry all ten proof steps: quotient
finiteness and surjective transitions; the identity stratum and covering with the
constant stalk calculation; degree-zero cohomology; the K-flat regular-module
reduction and its canonical projections; one interval for all levels; the replete
surjective tower's Roos triangle; integral membership; raw rational and pair
objects; integral extension computed on the same finite quotient tower; and the
common-stage representative and inverse. In particular the integral proof plan does
not rely on uniqueness of an arbitrary map into a triangulated homotopy limit.

Edge cases checked independently:

- Empty Y: no nonemptiness instance is required. Stalk quantification is vacuous;
  the empty cohomological support satisfies containment in [0,0]. The imported
  constructibility convention allows one empty stratum. No equality with {0} is
  asserted, and zero coefficient objects are allowed.
- Positive levels: Lean n=0 is exponent one, not exponent zero. Every positive
  quotient in the node is covered. The zero ring at exponent zero is outside this
  node's quantification, so omitting it does not remove a case.
- Identity stages: ι may be the identity and h is non-strict inclusion. Both the
  associator and T_(L,L) are retained in the common-stage class. Ramified extensions
  are included; no uniformizer equality or ramification-one instance is assumed.
- Characteristic: only l is prime and, where the global datum is used, l != D.p.
  There is no condition on the characteristic of Y, no finite type or separation,
  and no field hypothesis on a coefficient ring in place of A_(E,n).
- Sizes: d, u, v are explicit bound universe variables. Ω for the fixed algebraic
  closure has independent universe v. Finite coefficient fields admit the recorded
  small model in the scheme universe u by their finite basis. Geometric stalks use
  the dependency's Type u geometric points; every scheme point has such an
  algebraically closed residue-field extension. The small pro-etale site still has
  objects in u+1 and morphisms in u. No extra size equality is imposed.

Independent reuse searches (not just the first worker's searches):

- `msearch.py Q26 <item> leanfinder "The regular module of an inverse limit of
  finite constant coefficient rings on the pro etale site is derived complete and
  constructible"`: eight hits about BDeRham, formal etaleness and completions;
  no statement of this lemma.
- `msearch.py Q26 <item> loogle "SheafOfModules.unit"`: found the actual existing
  regular module, `unitHomEquiv`, and free-sheaf constructions. I opened their
  Mathlib source; the delivered helpers use these constructions directly.
- `msearch.py Q26 <item> leansearch "A regular sheaf of modules placed in degree
  zero is a constructible complex on the pro-etale site"`: general module sheaves,
  constant sheaves and quasicoherence; no matching coefficient theorem.
- `rg -n -i` with `constant.{0,45}constructible`, its reverse,
  `unit.{0,35}constructible`, its reverse, and `regular.{0,35}module`, over the
  upstream WeilConjectures tree, side `lean/Sheaf`, and Mathlib's module-sheaf and
  algebraic-geometry site sources. I opened upstream
  `ConstructibleSheaf/Monoidal.lean:161`: `isConstructibleSheaf_unit` is for
  `X.smallEtaleTopology` and ModuleCat-valued sheaves, not the present completed
  pro-etale derived/rational/common-stage statement. It is not an exact replacement.
- I also read `coord/pefw-upstream-framework.md` and inspected the side framework's
  pro-etale module-object definitions: `IsConstructibleModuleObject` and
  `boundedConstructible` concern internal modules and local finite presentations.
  They do not state this inverse-limit completion, reduction-map, or raw pair claim.
  No module can be dropped in favor of an exact existing declaration.

No new nodes or dependency modules were present to review under H12/H13; none are
needed. The node has no `statement_change`, and I found no source-based correction
requiring one. The unchanged node's fields other than `lean` agree with the shared
base. I checked that `lean.statement` is verbatim the main theorem signature before
`:= by`; all twelve declarations are listed, all five theorem proofs are exactly
`sorry`, definitions have real data, docstrings have the source and owning blueprint
tag, no local notation/private definitions are introduced, and no line exceeds
100 characters. No variable or universe is left unbound.

Validation: from this sandbox,
`python3 /home/ubuntu/weil-launcher-nt/scompile.py Q26
lem-weil-constant-coefficient-objects-constructible
lean/Sheaf/Paper/ConstantCoefficientObjectsConstructible.lean` passed both wrapper
checks: sandbox 6.9 s, library 8.2 s, each within 60 seconds; no warnings or errors.
An initial invocation from the shared directory had a missing relative input path;
rerunning from the authorized sandbox corrected the invocation, without any source
change or direct compilation. Mismatches found: none. Repairs made: none to Lean
or node; appended this independent second reading only.
