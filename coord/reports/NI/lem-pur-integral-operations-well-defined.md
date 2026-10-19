## Worker report

The module `Sheaf.Paper.IntegralOperationsWellDefined` states
`WeilConjectures.integralOperationsWellDefined`. It constructs the strict finite
pullback and tensor towers, their natural transition maps, and the functorial
Roos complex before stating quasi-isomorphism invariance and descent. All
postponed proofs are named theorems with source references and proof plans;
definitions contain data. There is no statement correction or disputed claim.

Hypotheses and preliminary constructions, clause by clause:

- The prime is `(l : ℕ) [Fact l.Prime]`. The finite extension is `(E : Type u)
  [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]`. The recorded Padic
  coefficient construction supplies its valuation ring and maximal-ideal-power
  quotients (equivalently uniformizer-power quotients). There is no additional
  chosen uniformizer, residue characteristic restriction, or finite-field datum.
- Schemes have universe `t`, independently of `u`; coefficients and module
  sections have size `max u (t+1)`. Site objects remain in `t+1` and morphisms
  in `t`. The morphism is an arbitrary `(f : X ⟶ Y)` and `W` is arbitrary.
- `integralTowerModules l E W` uses the published
  `completedIntegralCoefficientSheafUnrestricted`. This is the actual inverse
  limit of finite constant sheaves. `integralOperationsRestrict` is the recorded
  `SheafOfModules.restrictScalars` along the completion's canonical projection,
  applied degreewise.
- Natural-number level `n` throughout this delivery means the paper's positive
  exponent `n+1`. `unrestrictedIntegralFiniteComplex` is ordinary scalar
  extension degreewise. `unrestrictedIntegralTransition` is uniquely determined
  by sending the sheafified tensor `s ⊗ x` to `ρ_n(s) ⊗ x`.
- `integralOperationsLevelPullback` is the module left adjoint of sectionwise
  pushforward with its canonical constant-section coefficient map. Thus it is
  precisely `f⁻¹(-) ⊗_(f⁻¹ A_Y) A_X`. Its adjunction unit is the named
  `integralOperationsPullbackGenerator`. The unique pullback transition sends
  each such generator to the generator of its finite reduction; completed
  linearity and local generation determine the entire map, including scalars.
- `integralOperationsTensorLevel` uses
  `(MonoidalCategory.curriedTensor _).map₂CochainComplex`, the recorded
  direct-sum total tensor, with sign `(-1)^p` on the second differential.
  The unique tensor transition sends each `(p,q)` total-summand generator
  `x ⊗ y` to `r_n(x) ⊗ r_n(y)`. Restriction to the completion follows tensoring.
- `integralOperationsRoos` is `CochainComplex.mappingCocone` of the recorded
  `towerTransitionEndomorphism`: this is exactly `Cone(1-s)[-1]`. The countable
  products of complexes are Mathlib's termwise products, not derived products
  inserted as an input assumption. `integralOperationsRoosMap` is the shifted
  cone map of the commuting product square; its named identity/composition
  theorems provide `integralOperationsRoosFunctor`.
- `integralOperationsPullbackComplexFunctor` and
  `integralOperationsTensorComplexFunctor` are respectively the functorial
  strict tower followed by that Roos functor. They are the displayed `T_f` and
  `T` on objects and induced chain maps.

Conclusions, clause by clause:

- `integralOperationsGoodComplex` is the conjunction of the published
  `CochainComplex.IsKFlat` and `∀ i, SheafOfModules.IsFlatOnSite (P.X i)`.
  Its `FullSubcategory` imposes exactly K-flatness and flat terms, with no
  boundedness requirement.
- The first conjunct of `integralOperationsWellDefined` quantifies over any
  two good complexes on `Y` and any chain map `α`. `QuasiIso α` implies
  `QuasiIso (integralOperationsPullbackComplexFunctor.map α)`.
- The second conjunct quantifies over four good complexes on `W` and maps
  `α, β`. Their two `QuasiIso` hypotheses imply `QuasiIso` of the total tensor
  Roos map on `(α, β)`.
- The existential `F` has domain `DerivedCategory (integralTowerModules l E Y)`
  and codomain the corresponding category on `X`. `G` has the product of two
  derived categories on `W` as domain and that category as codomain.
- The natural isomorphisms `e` and `d` compare the descended functors after
  `integralOperationsGoodLocalization` with the localized displayed complex
  constructions. Thus these are descent functors with their representative
  comparisons, not arbitrary functors with only an objectwise existence claim.
- For every competing pair `F', e'` (respectively `G', d'`) the theorem gives
  `∃! ι : F ≅ F'` (respectively `G ≅ G'`), with the equation obtained by
  whiskering `ι` on good representatives and then composing with the second
  comparison. This is exactly uniqueness compatible with the comparisons.
- The final two conjuncts quantify over arbitrary derived objects `K`, or
  `M,N`, good representatives, and isomorphisms from their localized
  representatives. They assert the published `IsDerivedLimit` property for
  `F.obj K` and `G.obj (M,N)`, using precisely the localized strict tower
  transitions. Hence each value, and every choice of K-flat resolution,
  has the specified derived-limit property.
- Chosen resolution values themselves define functors by transport through
  `e,d` and the invertible localized resolution maps. Step 7 of the proof
  docstring gives the action on arbitrary derived morphisms and the normalized
  comparison between two choices. No unprovided chain-map lift is assumed.

Dependency declarations used:

- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing`, with the publicly imported
  `Padic.coefficientExtensionRing` and its transition morphisms.
- `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`:
  `AlgebraicGeometry.Scheme.ProEt`, `ProEt.topology` and the constant-sheaf
  pro-etale framework, preserved through the inverse-image imports.
- `Sheaf.Paper.CompletedIntegralCoefficients`:
  `integralCoefficientSheaf`, `integralCoefficientCommRingSheaf`,
  `completedIntegralCoefficientSheafUnrestricted`,
  `completedIntegralCommRingSheafUnrestricted`,
  `completedIntegralCommRingProjectionUnrestricted`, and the coefficient-sized
  sheafification/locally-bijective instances.
- `Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact`:
  `AlgebraicGeometry.Scheme.ProEt.countableProducts_exact`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses`:
  `SheafOfModules.siteSheafTensorRight` (through `IsFlatOnSite`).
- `Sheaf.AlgebraicGeometry.ProEtaleCoefficientPullbackUniverses`:
  `coefficientProEtaleModulePullback` and `coefficientProEtaleModuleAdjunction`,
  supplementing and publicly retaining the recorded inverse-image module.
- `Sheaf.Paper.IntegralReductionTowerUnrestricted`:
  `integralTowerModules`, `unrestrictedIntegralFiniteComplex`, and
  `unrestrictedIntegralTransition`. This landed DAG notion is added to the
  item's `stmt_deps`; its existing specialized module is publicly retained.
- `Sheaf.Algebra.Homology.KFlat`: `CochainComplex.IsKFlat` and its general
  tensor infrastructure; `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`:
  `CochainComplex.exists_isKFlatResolutionIndependentCoefficients`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`:
  `SheafOfModules.IsFlatOnSite`.
- Mathlib `SheafOfModules.restrictScalars`, `DerivedCategory`,
  `DerivedCategory.Q`, `HasDerivedCategory.standard`,
  `SheafOfModules.monoidalCategory`, `CochainComplex.mapBifunctor`,
  `CochainComplex.ιMapBifunctor`, and `CochainComplex.mappingCocone`.
- `WeilConjectures.CategoryTheory.Triangulated.DerivedLimit`:
  `CategoryTheory.IsDerivedLimit`, `towerTransitionEndomorphism`.
- The scheme-morphism-properties dependency is a convention node, with no
  independent declaration; the theorem uses `Scheme` and its ordinary morphisms.

Proof imports preserve the plan: `ChangeOfRingsKFlatQuasiIso`,
`ChangeOfRingsKFlat`, `SiteDerivedTensorDescent`, `DerivedLimitExistence`,
Mathlib's pretriangulated two-out-of-three lemma, and localization predicate
universal properties. The constant-exactness proof dependency has no Lean
record; its source assertion is cited in the proof plan rather than postulated
as an extra statement hypothesis.

Edge cases checked:

- The first paper level is exponent 1, represented by Lean `n=0`; no exponent-0
  quotient has silently been inserted in the tower.
- Empty schemes, zero complexes, identity morphisms, arbitrary scheme morphisms,
  and `l` equal to a scheme's residue characteristic remain allowed. There is
  no properness, smoothness, characteristic, or finite-field assumption.
- Complexes are unbounded in both directions. The tensor totalization uses
  coproducts over all pairs with fixed sum, including infinitely many summands.
- Coefficient field size is independent of scheme size. The extra interfaces
  preserve the small pro-etale site rather than identifying its two universes.
- Uniqueness is relative to the natural representative comparisons. It does
  not assert uniqueness of arbitrary maps of distinguished triangles (which
  Stacks explicitly warns against).

Searches for an existing exact statement:

- `msearch.py leanfinder`, query "K-flat resolutions completed tensor product
  pullback inverse limit of finite coefficient reductions define functors on
  derived categories": eight generic Tor/flatness results, no exact match.
- `msearch.py loogle`, query `CochainComplex.mappingCocone`: twelve mapping-cone
  API results, used for the actual shifted-cone construction.
- `msearch.py leanfinder`, query "K-flat resolution invariance completed
  integral pullback tensor derived limit functor": eight generic results,
  including Tor and flat tensor exactness, no exact statement.
- `msearch.py loogle`, query `quasiIso, DerivedCategory, CochainComplex, derived
  limit`: the service reported unknown identifier `quasiIso`; this unsuccessful
  query is not evidence of absence.
- `msearch.py leansearch`, query "inverse limit of complexes cone of one minus
  shift preserves quasi-isomorphisms": service unavailable (Internal Server
  Error); no absence verdict is inferred.
- `msearch.py grep`, query `mappingCocone|towerTransitionEndomorphism` in
  `Algebra/Homology`: fourteen mapping-cocone hits, no completed-integral
  operations statement. Direct `rg` searches of Mathlib, upstream
  `WeilConjectures`, and side `lean/Sheaf` for integral operations, completion,
  reduction towers and the item id found the recorded ingredients, not this
  exact invariance/descent theorem. The exact helper declarations were read
  before use. Search transcripts are retained in `searches.jsonl`.

Source reading included the blueprint's smooth-purity unit, Stacks
`sites-cohomology.tex` (K-flat resolutions and invariance on the other side),
and `derived.tex` (the derived-limit definition and exact-product comparison).
The full proof plan distinguishes strict chain-level functorial Roos from
non-functorial choices of an abstract triangulated cone.

## Dependency modules

`def-weil-integral-reduction-tower`: the recorded tower requires `D` and `l ≠ D.p`,
which the consumer and the node's coefficient construction do not require.
`IntegralReductionTowerUnrestricted` publicly imports the old module and uses
the already published unrestricted completion. Its ordinary reduction witness
is the existing canonical change-of-rings witness; its tensor generators and
unique prescribed transition give the same tower with no irrelevant datum.

`def-weil-proetale-inverse-image`: the recorded API is at coefficient size
`t+1`, whereas `E` has independent size `u`. `ProEtaleCoefficientPullbackUniverses`
publicly retains the existing general inverse-image interface and adds the
constant-coefficient specialization in `max r (t+1)`. Its right adjoint uses the
canonical map from constant sections, and its left adjoint is determined up to
canonical unit-compatible isomorphism by the adjunction. Its small-model data
use the original pro-etale site with object universe `t+1` and morphisms `t`.

`def-pc-kflat-complex`: the compilation overlay initially selected an older
specialized artifact and rejected the independent-coefficient resolution's tensor
structure. The sibling `KFlat` file is the current published source with unchanged declarations and bodies,
with the recorded seven declarations and relative-smallness interface retained.

`lem-pc-kflat-resolution`: include the current published
`KFlatResolutionIndependentCoefficients` source with unchanged declarations and bodies in the coherent overlay.
It retains K-flatness, flat terms, quasi-isomorphism and degreewise epimorphism.

`def-pc-flat-sheaf-modules`: the overlay selected the old specialized artifact.
Include the current published `FlatOnSite` source with unchanged declarations and bodies, retaining the
independent ring/module sizes and exact sheafified tensor definition.

The main module locally disables the overly specialized generic Grothendieck
sheafification instance during elaboration and uses the published
coefficient-sized instances. It introduces no file-local definition, notation,
or instance declaration, and exports no removal of an instance. All instance
terms in signatures are public declarations available to downstream files.

`lem-pur-derived-change-of-rings`: the sorted dry-run compilation reported a
missing `DerivedChangeOfRingsIndependentCoefficients.olean` when recompiling
`IntegralDerivedReduction`. Include the current published source with unchanged declarations and bodies as
an additional sibling overlay. It retains ordinary scalar extension on both
objects and maps, its additivity, quasi-isomorphism invariance, and the full
derived-functor/universal comparison statement. The already landed node is
added to `stmt_deps`; its named canonical scalar-extension witness is used by
the unrestricted reduction-tower dependency module. This is a compilation
artifact reconciliation, not a different derived change-of-rings construction.

`def-weil-integral-derived-reduction` and
`lem-weil-integral-reduction-tower-well-defined`: retain the current published
sources with unchanged declarations and bodies as coherent sibling overlays for the original specialized
tower import. The dry run had next reported the missing compiled
`IntegralReductionTowerWellDefined` dependency. These two unchanged interfaces
supply the full derived reduction, canonical chain maps, and their
representative comparisons; their already landed DAG nodes are added to
`stmt_deps`. This keeps the whole original tower interface available alongside
the unrestricted strict-complex construction.

The six published overlay modules additionally receive a module-docstring paragraph
explaining their independent-universe integral-operations application. Their
mathematical declarations, signatures, bodies and proof plans are unchanged.
This makes each interface repair an explicit, reviewable source/documentation
change in the delivery, as required by preflight.

## Second reading by NI

I read the node and the three new modules independently, then checked every
statement-dependency signature and all six supplied published overlay modules.
The Lean says what the node says. No mathematical statement or Lean construction
needed changing; this reading adds this report and independent search evidence.
There is no statement_change and no new definition node to audit.

Object/hypothesis/conclusion checklist (the node's order):

1. Prime ell, finite field extension E/Q_ell, its integer ring, uniformizer and
   positive quotient levels: `(l : ℕ) [Fact l.Prime]`, `(E : Type u) [Field E]
   [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]`. I opened
   `Padic.coefficientExtensionRing`, `coefficientExtensionIdeal` and
   `coefficientExtensionTransition`, not just the finiteness wrapper recorded
   as the dependency's main declaration. The ideal is the power of the span of
   the recorded uniformizer. Its quotient factor map is exactly reduction.
   Verdict: same coefficient data; Lean level n is paper exponent n+1.
2. Arbitrary scheme W, small pro-etale site, completed ring, projections,
   restriction and derived category: `integralTowerModules l E W` is
   `SheafOfModules` over `completedIntegralCoefficientSheafUnrestricted`, whose
   definition is `limit (integralCoefficientSheafSystem ...)`. I read the
   system, its projections and its commutative presentation in
   `CompletedIntegralCoefficients`. `integralOperationsRestrict` is Mathlib
   `SheafOfModules.restrictScalars` followed by `mapHomologicalComplex`.
   `DerivedCategory` uses standard localization. Verdict: actual inverse-limit
   ring, same scalar actions and unbounded derived category, no auxiliary
   finite-field datum or characteristic inequality.
3. An arbitrary strict tower C with maps C_(n+1) to C_n, and the termwise
   product map 1-s: `integralOperationsTowerStep`, `integralOperationsRoos`,
   and `integralOperationsRoosMap`. I read the current published
   `towerTransitionEndomorphism` and `IsDerivedLimit` through scompile's
   source reader. The former is identity minus the product shift, and the
   latter existentially supplies the two outer arrows of the distinguished
   Roos triangle. Mathlib `mappingCocone` is the shifted mapping cone.
   Verdict: the specified strict construction, with termwise products.
4. P_n and coefficient-induced reduction: the object and map equalities in
   `derivedChangeOfRingsIndependentCoefficients` fix the ordinary functor
   chosen by `unrestrictedIntegralReductionFunctor` to sheafified scalar
   extension, including its action on morphisms. The theorem
   `unrestrictedIntegralTransition_existsUnique` fixes the natural chain map
   by s tensor x mapping to rho(s) tensor x. Verdict: canonical termwise
   reduction and its actual transitions, not an arbitrary tower.
5. Arbitrary f:X to Y and finite module inverse image: f has no property
   instance. `integralOperationsLevelPullback` uses
   `coefficientProEtaleModulePullback` for the lifted finite ring. Its right
   adjoint is sectionwise pushforward with the explicitly constructed
   constant-section ring map; `Adjunction.ofIsRightAdjoint` provides its unit.
   This is the module pullback along the adjoint coefficient structure map.
   `integralOperationsPullbackTransition_existsUnique` prescribes its action
   on unit generators. Completed linearity fixes scalar multiples because
   the completion projection is locally surjective. Verdict: the node's
   tensor-formula module inverse image and its coefficient-compatible maps.
6. T_f(P): `integralOperationsPullbackTowerFunctor` has level
   `unrestrictedIntegralFiniteComplex` followed by degreewise module pullback
   and scalar restriction. `integralOperationsPullbackComplexFunctor` follows
   it by Roos. Verdict: all three operations in the displayed order.
7. T(P,Q): `integralOperationsTensorLevel` reduces both inputs, applies
   `curriedTensor.map₂CochainComplex`, and restricts scalars. I checked the
   section tensor and the `ιMapBifunctor` injections used to specify its
   transition. `integralOperationsTensorTransition_existsUnique` requires
   x tensor y to map to r(x) tensor r(y) in every bidegree. The standard
   totalization uses coproducts and the sign (-1)^p. The tensor tower then
   passes through the same Roos functor. Verdict: direct-sum total tensor
   and exactly the induced tower maps in the node.
8. Clause (1), pullback: `integralOperationsGoodComplex` is exactly
   `CochainComplex.IsKFlat P ∧ ∀ i, SheafOfModules.IsFlatOnSite (P.X i)`.
   The first conjunct of `integralOperationsWellDefined` quantifies over
   arbitrary two such complexes and an arbitrary quasi-isomorphism alpha,
   and asserts `QuasiIso` of the actual pullback-complex functor map.
   Verdict: no boundedness, extra flatness of f, or omitted input condition.
9. Clause (1), tensor: the second conjunct quantifies over four good
   complexes, alpha and beta and both quasi-isomorphism hypotheses, and
   asserts `QuasiIso` for the functor's map `(alpha,beta)`. Verdict: both
   variables and both hypotheses, with the required simultaneous conclusion.
10. Clause (2), functorial descent: F has domain D(Y) and codomain D(X);
    G has domain D(W) times D(W) and codomain D(W). The natural isomorphisms
    e and d compare precomposition by good-representative localization with
    `integralOperationsPullbackOnGood` and `integralOperationsTensorOnGood`.
    Verdict: genuine natural comparisons on objects and maps. The proof's
    transport formula defines the displayed chosen-resolution values on
    arbitrary derived morphisms; no functorial chain-map lifts are assumed.
11. Clause (2), independence and uniqueness: for every competing F',e' or
    G',d', the conclusion is `∃! ι` with the equation that whiskering iota
    and composing the second comparison equals the first comparison.
    Verdict: precisely uniqueness relative to the comparison data. This
    does not assert uniqueness of a triangulated cone completion.
12. Clause (2), every value a derived limit: the final two conjuncts quantify
    over arbitrary K or M,N, arbitrary good representatives and isomorphisms
    from their localized representatives. They assert
    `integralOperationsDerivedLimitProperty` for F(K) or G(M,N), with the
    localized transitions of those very strict towers. Verdict: every
    representative choice and the correct derived-limit predicate.

Source and edge-case checks: I read sites-cohomology.tex at 06YS, 06YT and
0G7E, including their ringed-site/topos hypotheses; no Noetherian or scheme
morphism condition is assumed there. I read derived.tex at 08TC and 07KC:
exact countable products justify the termwise model, and abstract derived
limits only have nonunique isomorphisms. I also read Bhatt--Scholze pp. 22--24
and 50--51 (3.4.10, 3.5.2, 6.5.9(4)). The qcqs hypothesis in the latter
lemma belongs to its completed-pullback adjunction context; this node only
asserts the general invariance/descent construction proved using Stacks and
exact pro-etale products, not that adjunction. No qcqs assumption is needed
in this statement.

Empty schemes, zero complexes and identity maps are included. The tower is
indexed by all natural numbers with first exponent 1, so paper exponent 0
is correctly absent; no nonempty assumption on an unrelated set appears.
Complexes are unbounded and tensor total degrees may have infinitely many
summands. The independent universes t,u retain pro-etale objects in t+1,
morphisms in t and coefficients/modules in max u (t+1); there is no hidden
universe equality, characteristic restriction, properness or smoothness.
All variables/universes are explicitly bound. I checked each of the nine
lean.statement strings is verbatim in its module and all lines meet the
100-character limit.

Dependency delivery audit: `def-weil-proetale-inverse-image` retains the
previous general ring interface through a public import and supplies the
needed constant-coefficient version in independent universes. Its adjunction
fixes the functor up to the normalized unique isomorphism, so this is not an
unconstrained Nonempty choice. `def-weil-integral-reduction-tower` similarly
retains the original augmented derived tower through its public import and
adds the unrestricted strict reduction core; the original augmentation,
canonical comparisons and independence statements remain available.
The six other dependency modules are identical to the published source in
all declarations, signatures, bodies and proof plans; I compared them
line by line and found only the reported explanatory module-docstring
paragraphs. In particular K-flatness still tests all acyclic complexes,
flatness still means exact sheaf tensor, the resolution still gives flat
terms and degreewise epis, and change of rings fixes both objects and maps
and retains its derived universal property. A separate authorized compile
with only the three new modules failed on the missing published
IntegralReductionTowerWellDefined.olean; this independently confirms the
need for the supplied coherent source overlays. No private copy of a
mathematical notion, hollow definition, extra axiom or filled proof occurs.
All postponed helper theorems have source/blueprint docstrings and proof
plans, are recorded under their owning node's lean.declarations, and serve
that node's stated constructions.

Independent searches: LeanFinder query "Functorial homotopy inverse limit
of finite coefficient sheaf tensor complexes preserves quasi-isomorphisms"
returned generic complex-localization results, not this statement. Loogle
`CategoryTheory.IsDerivedLimit` reports an unknown identifier (not absence
evidence); I instead read that actual published declaration. Wrapper grep
`completedTensor|homotopyInverseLimit|integralOperations` found no match.
Direct rg searches in Mathlib, upstream WeilConjectures and lean/Sheaf for
Roos, homotopy limits and completed tensor found `RoosComplex`,
`DerivedLimitTowerRoosTriangle`, `IntrinsicKoszulCompletion` and upstream
`Pretriangulated.IsHomotopyLimit`; I opened their declarations. They concern
K-injective tower comparison, a Koszul-specific complex, or abstract Milnor
triangles, not these finite-reduction operations or their descent theorem.
The existing generic cone and transition-endomorphism constructions are
used directly. No exact statement exists to attach in place of this module.

Validation: scompile.py compiled every supplied module, separately in
import order, cleanly with nice 19, two threads and the unchanged 60-second
per-file limit. The maximum reported file time was 9.9 seconds. The
current server source was used for published declarations absent from the
older local upstream checkout. No Lean repair or node statement correction
was necessary; no target unit was changed.
