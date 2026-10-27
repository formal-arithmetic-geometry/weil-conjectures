## Worker report

The module `Sheaf.Paper.IntegralImmersionPullbackNormalization` states
`WeilConjectures.IntegralImmersionNormalization.integralImmersionPullbackNormalization`.
Its namespace also exposes the actual coefficient transports, the actual strict
completion comparison, and the proposition and comparison structures used in the
signature. The mathematical statement is unchanged. No dependency is restated and
the existing normalization helpers are assigned an explicit definition owner.

The module was recovered from the interrupted sandbox, and the previous compile log
was inspected before retrying. A fresh prescribed `scompile.py` run succeeded:
the sandbox check took 41.2 seconds and the library-module check 48.3 seconds.
There were no errors or warnings. All theorem proofs in this delivery are `sorry`.
There are two: the main theorem and `moduleRoundTrip_exists`. The latter specifies
the coefficient round trip uniquely on every section; it is a normalization helper
of this item, not a choice of an undetermined object. All definitions have real data.

The sources read were the item's complete node, its statement dependencies and their
recorded source declarations, the current blueprint's
`sec-smooth-purity/sk-prop-sf-localization/prop-sf-open-closed-triangle-all-stages.proof.md`,
especially the integral and rational paragraphs, and local `proetale.tex` at
`lemma-pushforward-Noetherian-case` (099N) and `lemma-closed-immersion` (09AA).
The module docstring and main theorem docstring retain the six-step proof plan:
Noetherian geometry; finite DVR quotients; ordinary/strict completion comparison;
integral/strict comparison; signed Roos shifts; exactness, linearity and reductions.

Hypothesis and clause correspondence:

| Node text | Lean rendering |
| --- | --- |
| Global finite-field datum and fixed algebraic closure k | `D : FiniteFieldDatum.{u}`, using `D.k`; the structure includes p, the prime proof, q=p^a, the finite base field and its algebraic closure. |
| Prime l different from p | `l : ℕ`, `[Fact l.Prime]`, `_hl : l ≠ D.p`. |
| Finite extension E/Q_l | `E : Type u`, `[Field E]`, `[Algebra ℚ_[l] E]`, `[FiniteDimensional ℚ_[l] E]`. |
| Its valuation ring, uniformizer and positive quotients | The recorded `Padic.coefficientExtensionIntegers`, `coefficientExtensionUniformizer`, `coefficientExtensionRing` and `coefficientExtensionIdeal`; no alternate ring or uniformizer. |
| Separated finite-type k-scheme X | `aX : X ⟶ Spec (CommRingCat.of D.k)` with `IsSeparated`, `LocallyOfFiniteType` and `QuasiCompact` instances. The explicit structure map is needed to express the finite-type hypothesis. |
| Closed immersion i and complementary open immersion j | `i : Z ⟶ X`, `[IsClosedImmersion i]`, `j : U ⟶ X`, `[IsOpenImmersion j]`, and `_hcomplement : Set.range j = (Set.range i)ᶜ`. |
| X,U,Z Noetherian and qcqs; j quasi-compact | The six `IsNoetherian`/`QuasiSeparatedSpace` conjuncts and `QuasiCompact j`. Noetherian schemes include quasi-compactness. These are conclusions, not additional hypotheses. |
| Finite perfect quotients with [R --t^n--> R] | `FinitePerfectQuotients`: every positive quotient is finite; a strictly [-1,0] finite-free complex has the specified scalar differential and a quasi-isomorphic quotient augmentation. Thus perfectness is witnessed by the full specified free resolution. |
| B_T is the inverse limit of finite constant coefficient sheaves | Existing `completedIntegralCommRingSheafUnrestricted`, `scalarReductionSource` and `pbcIntegralDatum`; `completedRingIso` and `finiteRingIso` identify their published presentations by their finite projections. |
| C_T is the full derived-complete integral constructible subcategory with uniform bounds | The existing `sfIntegralConstructibleCategory` and `sfIntegralConstructible`; these require derived completeness, constructibility of every positive reduction and one common interval. |
| Canonical coefficient isomorphisms for i,j | `coefficientIso` and `finiteCoefficientIso` compose the existing normalized ring isomorphisms, rather than hypothesizing an arbitrary isomorphism. |
| Constants, projections and transitions preserved | `Comparison.coefficients : CoefficientNormalization`: the adjoint ring map sends `integralScalarConstant ... r` to the same constant section; the completed-projection equation holds at every n; the finite transition square holds for every arrow of the quotient index category. |
| Ordinary module inverse image g_o* | `ordinaryModule` is the recorded `ImmersionCompletedPullback.modulePull`, transported along the fixed coefficient-ring isomorphisms; `ordinary` applies `mapDerivedCategory` to this exact termwise functor. `ordinaryPresentation` uses the existing counit-normalized `derivedIso`. |
| Strict quotient-tower completed pullback g_c* | `completed` is exactly `back ⋙ pbcActualStrictCompletedPull ⋙ transport`; it uses the published strict quotient functor, not a chosen cone or unspecified completed functor. |
| Specified integral pullback g_R* | `integralDerivedPullback`, the ambient functor underlying the recorded `constructibleIntegralPullback`. The output constructibility is a conclusion here, so no additional residue-field invertibility instances are assumed. |
| Natural isomorphism gamma: g_R* -> g_c* | `Comparison.gamma`, on the full constructible source and with ambient completed-coefficient target. `gamma_normalization` specifies it as the existing integral comparison followed by the fixed strict/reflector comparison and the coefficient round trip. |
| gamma identifies defining strict-tower projection maps | `integralComparison : IntegralCompletedComparison.Comparison` contains the normalized finite tensor generators, representative computation maps and its `projections` equation; `gamma_normalization` carries precisely that comparison to the original strict construction. `complete_back` supplies its completeness domain for every constructible object. |
| Actual completion isomorphism c: g_o* -> g_c* | `Comparison.c`, with `c_hom` identifying its hom with the full-source restriction of `completionComparison`. That transformation is defined directly from `pbcActualStrictCompletedPullUnit`, after the fixed ordinary presentation comparison. |
| Completion finite quotient projections | `completion_projections` identifies c followed by each actual finite projection with the tensor-unit quotient map, transported by the same coefficient functor. |
| Completion quotient transitions | `completion_transitions` states the equation for all b,a and a≤b, including equal indices and every successive quotient. |
| Shift compatibility of gamma and c | `integralComparison.chainShift_coordinates` and `derivedShift_descent` fix the integral shift to its signed Roos construction; `gamma_shifts` and `completion_shifts` are `NatTrans.CommShift` for these structures and ordinary termwise shifts. |
| Composite c^-1 gamma identifies canonical integral/termwise shifts | The composite is the actual `gamma ≪≫ c.symm`; `composite_shifts` explicitly asserts its `NatTrans.CommShift` for the specified integral shift and ordinary termwise shift. No extra arbitrary integral shift is substituted. |
| Exactness | `ordinary_exact`, `integral_exact`, `completed_exact` assert `Functor.IsTriangulated` on the recorded full constructible source. The latter two use exactly the shift structures in the comparison equations. |
| R-linearity | The three `Functor.Linear (Padic.coefficientExtensionIntegers l E)` fields use the published constant-section linear structures, including the ambient structure and full-subcategory structure. Components of the comparisons are maps over the completed ring sheaf. |
| Preserve completeness and carry C_X into C_Y | The three clauses of `constructible` assert the entire recorded target predicate, which includes derived completeness. Both isomorphisms have constructible source; their ambient codomain includes exactly the full constructible essential image required here. |
| Same finite-reduction interval [a,b] for integral pullback | `interval` quantifies over the given integers a,b and transfers `HasReductionInterval` without replacing the interval or choosing another bound. Every positive quotient is included as level n+1. |
| Both immersions | Main conclusion includes `Nonempty (Comparison l E i)` and `Nonempty (Comparison l E j)`. These are existence of normalized isomorphisms and their properties, not a definition choosing data from a mere Nonempty theorem. |
| No constant-R replacement | Every ambient category is `DerivedCategory (scalarReductionSource l E T)` or the published isomorphic `PbcCompletedDerived`. Constant sheaves occur only in the finite quotient and scalar-section constructions. |

The coefficient restriction round trip is spelled out so that no equality of distinct
scalar actions is hidden. `moduleRoundTrip_exists` fixes its identity on all sections;
`moduleRoundTrip` selects that unique normalized iso; `roundTrip` descends it by the
existing exact-functor localization. It has the same source/target completed rings as
the finite-projection-normalized `completedRingIso`. Its proof docstring states the
sectionwise construction, naturality and uniqueness.

Dependency declarations used:

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`: the reexported coefficient
  ring, ideal and uniformizer constructions and `Padic.finite_coefficientExtensionRing`.
- `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`: the recorded completed
  coefficient sheaf and constant-section map, with positive quotient projections.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `ProEt.topology`;
  standard scheme/morphism classes render the convention-only morphism-property node.
- `Sheaf.Paper.SfIntegralConstructible`: `sfIntegralConstructible`,
  `sfIntegralConstructibleCategory`, plus their recorded reduction/support notions.
- `Sheaf.AlgebraicGeometry.ProfiniteCoefficientInverseImage`: the existing inverse
  image and coefficient-comparison interfaces used by `pbcIntegralDatum`.
- `Sheaf.AlgebraicGeometry.ProEtaleRingSheafOperations`: recorded module inverse image;
  its intrinsic module-sheaf presentation is the dependency's
  `ImmersionCompletedPullback.modulePull`/`proEtaleRingModulePullback`.
- `Sheaf.Paper.PbcQbarCompletedPullback`: reexports the published integral strict
  functor `pbcActualStrictCompletedPull` and actual unit
  `pbcActualStrictCompletedPullUnit`; the Qbar restriction is not used.
- `Sheaf.Paper.DerivedPullbackTensorHom`: the specified integral construction
  `integralDerivedPullback`, underlying `constructibleIntegralPullback`.
- `Sheaf.Paper.IntegralPullbackCompletedComparison`:
  `IntegralCompletedComparison.Comparison`, its gamma, finite normalization,
  projection and shift fields and `towerIso`.
- `Sheaf.Paper.SfImmersionCompletedPullbackComparison`: `completedRingIso`,
  `finiteRingIso`, `transport`, `modulePull`, `derivedIso`,
  `actualCompletedProjection`, `reductionUnit` and `reductionTransition`.
- `Sheaf.Paper.SfIntegralConstructibleLinear`: the published ambient and full
  subcategory constant-section linear instances. Its triangulation dependency
  `Sheaf.Paper.SfIntegralConstructibleTriangulated` supplies the inherited shifts.

The statement dependencies cite the definition owners
`def-pod-integral-completed-comparison-data` for `Comparison`, `Complete` and
`towerIso`, and `def-sf-integral-constructible-linear-structure` for the ambient
and full-subcategory linear instances. The genuine triangulation instance theorem
`lem-weil-integral-constructible-triangulated` remains a statement dependency.
The comparison existence theorem stays a proof dependency. The completed ring
presentation isomorphisms cite `def-a1-integral-completed-pullback-interfaces`.
The ordinary/strict normalization helpers cite the new existing-definition node
described below. The statement also cites `def-weil-pbc-bounded-constructible-tower`,
`def-weil-proetale-inverse-image`, `def-sf-completed-integral-scalar-action`,
`def-weil-pbc-adic-coefficient-datum` and `def-weil-pbc-four-corners` for the scalar
restriction, site inverse image, constants, quotient coefficient datum and ordinary
pullback/reduction interfaces it uses. The public import of
`Sheaf.Paper.SfImmersionCompletedPullbackComparison` exposes these constructions;
its visibility is the sole Lean-file change in this repair. All declaration bodies,
signatures, universes and docstrings are preserved. Every other node field,
including its natural-language statement and proof, is retained.

Edge cases checked before finalizing the signature:

- Empty X, U or Z are allowed. No nonempty or chosen-point hypothesis occurs;
  complement, exact functors, constants, limits and the full subcategories still type.
- The zero complex and zero morphisms are included. No nonzero-rank condition occurs
  in the finite-free resolution or in the linear/triangulated assertions.
- Level zero in Lean denotes exponent one. Positive exponent n in
  `FinitePerfectQuotients` has the explicit 1≤n hypothesis; exponent zero is not asserted.
- Negative, zero and positive shifts all use ℤ, with the normalized signed Roos shift.
- Transitions include a=b, successive indices and arbitrary larger quotients.
- `HasReductionInterval` allows a>b as well; then the support is empty. No case is
  excluded by an unnecessary a≤b hypothesis on a supplied reduction bound.
- The prime l is not assumed invertible in an additional field or stalk binder:
  this follows from the supplied global datum and scheme structure. Residue-field
  invertibility instances required by a restricted API are not added as hypotheses.
- Site objects retain universe u+1 and morphisms u; coefficient rings use their
  existing u+1 lift. All variables and universes are explicitly bound, with
  `autoImplicit false`. No file-local notation, private definition or local instance
  appears in this delivery.

Searches (also recorded automatically in the sandbox searches.jsonl):

- LeanFinder, "Integral immersion pullback agrees with ordinary inverse image and
  strict completed pullback with quotient projections and shifts": eight hits on
  ordinary scheme immersions and pullback diagrams, no completed-coefficient result.
- LeanSearch, "Integral completed coefficient pullback for open and closed immersions
  is exact and linear": eight hits on scheme ideal sheaves, geometric open-immersion
  pullbacks and integral morphisms, no matching coefficient-derived statement.
- Loogle, `Functor.CommShift, Functor.IsTriangulated, Functor.Linear`: no hits;
  service reported unknown identifier `Functor.CommShift`. Earlier recorded
  query `"pullback", "exact"` returned only categorical exact-short-complex and
  pullback-of-colimit results, not this statement.
- msearch grep, `completed.*pullback|pullback.*completed` in Mathlib
  AlgebraicGeometry: zero hits. Earlier broad grep also returned two unrelated order hits.
- rg in `lean/WeilConjectures` for immersion/pullback: finite coefficient, condensed,
  adic and etale-localization interfaces, none the three normalized completed-ring
  functors. Literal node-id grep in that source found no declaration.
- rg in `lean/Sheaf` for integral/completed/ordinary pullback identified and led to
  reading the existing two comparison modules, ordinary completed integral pullback,
  the coefficient presentations and the linear/triangulated interfaces. None states
  the present conjunction with both complementary immersions, geometry, finite-free
  quotients, actual completion map, full gamma normalization and unchanged interval.

There is no statement correction and no STATEMENT-DISPUTED flag. No declaration
from a known unusable record is rebound; all the recorded constructions used here
were read in the shared sources and the delivered file compiles against the live build.


## Repair of returned head 7373c8c68b1c

The prescribed first dry run of the saved packet succeeded at commit b16b6c58f4c.
That mechanical success did not discharge the independent ownership findings.
This packet makes the substantive R1/R2 changes requested by that return.

R1: replaced the comparison-existence and linear-coherence theorem citations in
`stmt_deps` with the two existing definition owners named above. Retained the
triangulation theorem citation, which the reviewer explicitly accepted. No proof
plan or theorem statement changed.

R2: added all six existing definition citations requested by the reviewer (the
coefficient-presentation interface and the five additional framework nodes), plus
one new existing-definition node for the unowned ordinary/strict helpers and their
body helpers. Promoted the existing comparison-module import to `public import`.
The new node is a record of published declarations, so adds no Lean file, theorem
proof or duplicate definition. The saved main node was compared fieldwise with
current shared main: its original delivery changes were only `lean` and the three
added `stmt_deps`; the repair still changes only `lean` and `stmt_deps`.

## New nodes

`def-sf-immersion-completed-pullback-normalization-data` records, with
`existing: true`, `modulePull`, `derivedIso`, `actualCompletedProjection`,
`reductionUnit`, `reductionTransition`, and their actual construction helpers in
`Sheaf.Paper.SfImmersionCompletedPullbackComparison`. The primary signature is
copied verbatim from `actualCompletedProjection`; the record lists the object
equality/naturality helpers, the identity-on-tensor module iso, the unique counit
normalization, finite and restricted comparisons, restricted reduction, tower
evaluation, the actual limit projection and the unique unit-normalized strict iso.
These helpers determine canonical maps and do not assert the immersion theorem.

The source is the current blueprint localization proof's integral-stage pullback
reductions and rational-stage exact integral pullbacks, with Stacks 099N and 09AA.
The definitions have arbitrary scheme maps, and positive quotient level n means
exponent n+1. The unit exists for every object, even when not complete; its
invertibility is not assumed. Transitions include equal indices, and the actual
projection is the composite in the existing body, retaining the quotient action.
Empty schemes, zero objects and all coefficient/site universes are unchanged.

Fresh prescribed searches: LeanSearch returned eight hits, including ordinary
adic completion and sheaf module pullback units; LeanFinder returned eight hits
on condensed counits, ordinary adic evaluations and generic module adjunctions;
neither gives the completed-sheaf normalization. Mathlib grep for the five helper
names in AlgebraicGeometry returned zero hits. The exact query strings and result
names are preserved from searches.jsonl in the new node's mathlib_searches.
DAG rg found only the owning theorem node, not a definition owner; blueprint search
for "completed pullback" returned 25 nodes and none owns these normalization
helpers. Project rg found the exact existing declarations in the comparison module;
upstream hits concerned unrelated curve reduction units. Therefore the new record
uses those declarations without copying any implementation.

## Self-check by Q72

Re-read the returned findings against the main node, the unchanged declaration
signatures and the published source of every new ownership record. R1's two
statement uses are definition/instance uses, now cited to those owners. R2's five
helpers and body helpers are recorded in the new definition node and exposed by
the public import. The five additional framework owners and the existing completed
coefficient interface are all in stmt_deps. The main theorem, every comparison
field, finite projection normalization, shifts, exactness, linearity, completeness
and unchanged interval remain byte-identical. No statement correction or
STATEMENT-DISPUTED flag is required. No second agent was started, as instructed;
the maintainer supplies the independent reading.

## Second reading by Q72

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
