## Worker report

The module `Sheaf.AlgebraicGeometry.EtaleClosedOutputBounds` states
`AlgebraicGeometry.ProEtale.etaleClosedOutput_bounds`, with one whole-proof `sorry`.
It states the two implications independently, for the ordinary etale closed-support
right adjoint and its canonical comparison pullback. It does not define a new functor,
coefficient ring, constructibility condition, interval, or Tor predicate. There is no
statement correction, new node, or STATEMENT-DISPUTED finding.

### Hypotheses and clauses

| Node text | Lean rendering |
| --- | --- |
| Fixed algebraic closure of a finite field, ell different from the characteristic, fixed coefficient closure and finite extension, uniformizer and positive level | `P : WeilConjectures.PurityFiniteSetting.{u}`. Its `field` and `coefficients` supply the finite-field datum, prime and characteristic inequality; `extension` is an actual finite intermediate field of the fixed coefficient closure; `level_pos` gives n >= 1. `P.Ring` is the existing quotient by the chosen uniformizer power and `P.Coefficient` is its standard `ULift` for the small-site value universe. |
| Ordinary constant-A module derived categories | `Etale.DerivedCategoryModule P.Coefficient T` and `Scheme.proEtaleDerivedCategory Z P.Ring`. These are ordinary derived localizations, without completion, finite-Tor restriction, or etale-origin restriction on the pro-etale category. |
| Finite-type k-schemes Z and T | `Z.Over` and `T.Over` of `Spec (.of P.field.k)`, with `LocallyOfFiniteType` and `QuasiCompact` of both structure morphisms. These two properties express finite type; separatedness of either structure morphism is not assumed. |
| Closed immersion between the k-schemes | `i : Z ⟶ T`, `[IsClosedImmersion i]`, `[i.IsOver (Spec (.of P.field.k))]`. |
| Quasi-compact complementary open | `j : W ⟶ T`, `[IsOpenImmersion j]`, `[QuasiCompact j]`, and `_hij : Set.range i.base = (Set.range j.base)ᶜ`. No nonemptiness restriction is imposed. |
| c >= 0 and both ordinary etale open-complement conditions | `c : ℕ`, `_hc : Scheme.HasOpenComplementCondition P.Coefficient j c`. The first conjunct of this recorded predicate quantifies over every etale module sheaf M and q > c and gives vanishing of R^q j_* M. Its second conjunct says all integer-degree higher direct images of every constructible sheaf are constructible. Its D+ right-derived presentation on degree-zero objects computes these same higher direct images. |
| Ambient ordinary etale right adjoint i_e^! | `(R(Etale.lowerStar (ModuleCat.{u + 1} P.Coefficient) i)).rightAdjoint`. The existing instance `isLeftAdjoint_rightDerivedLowerStar_of_isClosedImmersion` supplies it. It is not a free parameter, a constructible-only adjoint, or an additional admissibility hypothesis. |
| K_e in D^b_c | `K : Etale.DerivedCategoryModule P.Coefficient T` and `_hK : Etale.DerivedCategory.isBoundedConstructible P.Coefficient T K`. This uses finite-value constructible strata in every degree and a finite cohomological interval. |
| C_e and C_p | Every occurrence of C_e is the actual right-adjoint value on K. C_p is `(finiteCoefficientIntrinsicDerivedComparison Z P.Ring).obj C_e`, the existing canonical exact inverse image into intrinsic constant-ring modules, not an arbitrary comparison object. No `let` binder obscures these objects. |
| All integer r <= s | `r s : ℤ`, `_hrs : r ≤ s`; negative degrees and r=s are included. |
| (a) premise: cohomology only in [r,s] | The first implication's premise is `_root_.DerivedCategory.homologyConcentratedIn r s K`, which is the inclusive cohomological interval. |
| (a) C_e in constructible interval [r,s+c+1] | `isBoundedConstructible ... C_e ∧ homologyConcentratedIn r (s + (c : ℤ) + 1) C_e`. The etale presentation explicitly conjoins constructibility with the interval. |
| (a) C_p in intrinsic constructible interval [r,s+c+1] | `WeilConjectures.constructibleInterval P.coefficients.l P.extension P.level P.level_pos Z r (s + (c : ℤ) + 1) C_p`. This is exactly the predicate underlying the recorded `intrinsicConstructibleIntervalCategory`, not a new interval definition. |
| (a) no finite-Tor hypothesis | Neither the common hypotheses nor the first implication contains any Tor condition. |
| (b) independent etale Tor premise | The second implication begins afresh with `Etale.DerivedCategory.hasTorAmplitudeIn P.Coefficient T r s K`. It does not take the premise or conclusion of (a) as input. |
| (b) bounded constructible C_e and its etale Tor interval | `isBoundedConstructible ... C_e ∧ hasTorAmplitudeIn P.Coefficient Z r (s + (c : ℤ) + 1) C_e`. |
| (b) intrinsically bounded constructible C_p | `Scheme.intrinsicFiniteTorsionConstructible P.coefficients.l P.extension P.level P.level_pos Z C_p`. |
| (b) pro-etale Tor interval, including the final displayed vanishing for every N | `Scheme.HasProEtaleTorAmplitude Z P.Ring C_p r (s + (c : ℤ) + 1)`. This existing predicate quantifies every cochain representative and K-flat resolution, and then EVERY degree-zero module sheaf M on the full small pro-etale site and EVERY integer degree outside the interval. Its `IsZero` conclusion is precisely the cohomology vanishing in the node. There is no origin, constructibility, or finiteness assumption on M. Consequently the final 'in particular' clause is included in the actual predicate, rather than weakened to etale-origin tests or replaced by a mere existential finite Tor interval. |

The original intrinsic Tor predicate is publicly retained in the recorded general
Tor-amplitude module, through `CoefficientProEtaleTorAmplitude` and
`ProEtaleTorAmplitude`. It is also exactly the predicate used in the recorded
`finiteTorConstructible` and `comparison_torAmplitudeIn_iff`. Using that existing
specialization does not introduce a second notion. A probe with the newer general
`HasRingedSiteTorAmplitudeOfUniverses` produced an underdetermined max-universe in
its additive-sheafification instances. The intrinsic predicate uses the same full
site and standard localization directly and compiles without any new universe
restriction, transport, assumed equality, or extra hypothesis. No source statement
needs to change.

### Dependency declarations read and used

- `Sheaf.Paper.PurityFiniteSetting`: `WeilConjectures.PurityFiniteSetting`, `.Ring`,
  `.Coefficient`, their ring instances and the finite-field/coefficient data.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`. This repairs
  the stale ambient-notation dependency as detailed below. `DerivedCategory.Plus`,
  `.Minus` and `.Bounded` are the existing t-structure subcategories.
- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`:
  `Scheme.proEtaleSiteComparison` and `Scheme.proEtaleSiteComparisonModules`.
  Its actual inverse image is the existing `ProEtale.comparisonUpperStar`.
- `Sheaf.AlgebraicGeometry.ProEtaleFiniteModuleIntrinsicComparison`:
  `finiteCoefficientIntrinsicComparison`, `finiteCoefficientIntrinsicRealization`,
  `finiteCoefficientIntrinsicDerivedComparison`. The latter is termwise inverse
  image followed by canonical constant-ring realization on the ordinary derived category.
- `Sheaf.Paper.IntrinsicFiniteTorsionConstructibility`:
  `Scheme.intrinsicFiniteTorsionConstructible`.
- `def-weil-scheme-morphism-properties` explicitly collects other definitions and
  defines no object of its own. Its relevant notions are Mathlib `IsClosedImmersion`,
  `IsOpenImmersion`, `LocallyOfFiniteType`, `QuasiCompact`, and `Scheme.Over`/`IsOver`,
  already imported by the corresponding geometric modules.
- `Sheaf.AlgebraicGeometry.OpenComplementCondition`:
  `Scheme.HasOpenComplementCondition`.
- `Sheaf.AlgebraicGeometry.EtaleClosedAmbientAdjoint`:
  `Etale.isLeftAdjoint_rightDerivedLowerStar_of_isClosedImmersion`.
- `Sheaf.AlgebraicGeometry.IntrinsicConstructibleIntervals`:
  `WeilConjectures.intrinsicConstructibleIntervalCategory`, a transparent alias of
  the existing `constructibleIntervalCategory` over `constructibleInterval` in
  `Sheaf.Paper.ConstructibleIntervalsUnordered`. The statement uses that very predicate.
- `Sheaf.AlgebraicGeometry.EtaleTorAmplitude`: existing
  `Etale.DerivedCategory.hasTorAmplitudeIn`, publicly imported from
  `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`.
- `Sheaf.Paper.FiniteTorAmplitudeSites`: `finiteTorConstructibleEtale`, with the
  existing intrinsic `finiteTorConstructible`/`finiteTorConstructibleCategory`.
  Their underlying Tor and constructibility predicates are used separately with
  the specified interval, rather than replacing it by an existential bound.
- `Sheaf.Paper.ConstructibleExceptionalInverseImage`: existing derived instances
  `PurityFiniteSetting.ringFinite` and `.coefficientFinite`. Its exceptional
  functor is not used: the statement uses the ordinary etale ambient right adjoint.
- Proof-only imports: `EtaleClosedSupportAmplitude.closedImmersion_rightAdjoint_amplitude`,
  `ProEtaleConstructibleOrigin.constructible_proEtale_origin`,
  `ComparisonPullbackExact.comparisonPullbackExact`,
  `EtaleClosedSupportTorAmplitude.closedImmersion_rightAdjoint_torAmplitude`,
  `ComparisonTorInterval.comparison_torAmplitudeIn_iff`, and the recorded general
  Tor predicate module `RingedProEtaleTorAmplitudeOfUniverses`. All remain plain
  imports for the stage-3 proof plan; statement dependencies are public imports.

I read the item and all ten statement dependencies (including their records and
available full source signatures/docstrings), the seven proof dependencies, the
current main-20261015 general-admissibility proof Step 2, and the ordinary etale
amplitude and Tor proof files in sec-six-functors-basics/sk-prop-a1-kummer. The
comparison uses the full small pro-etale site (objects Type (u+1), arrows Type u).
There is no restriction making these two universes equal.

### Edge cases

The empty closed subscheme and empty schemes are allowed: their module categories
are zero and both bounds hold. For i=id the complement can be empty and c=0;
the output bound [r,s+1] contains the original interval. For the origin in the affine
line with c=1, the usual degree-two closed-support output from a degree-zero input
lies in [0,2], so the sign and +1 are correct. Endpoints r and s+c+1 are included,
r=s is allowed, negative r,s are allowed, and c=0 is allowed. Positive levels
include n=1 and every n>1; the latter is why no finite-Tor premise was silently
introduced into (a). Nonseparated finite-type schemes are not excluded. Every
pro-etale test sheaf, including ones without etale origin, occurs in (b).

### Searches

- `msearch.py ... leanfinder "Closed immersion exceptional pullback cohomology and Tor amplitude bounds after comparison from etale to proetale"`: eight hits, including `IsImmersion.isPullback_toImage_liftCoborder`, etale-site pullbacks and ring etaleness; none states these bounds.
- `msearch.py ... loogle "AlgebraicGeometry.IsClosedImmersion, DerivedCategory"`: zero hits.
- `msearch.py ... grep 'closed.*(amplitude|Amplitude)|exceptionalInverseImage' AlgebraicGeometry`: zero Mathlib hits.
- `msearch.py ... leansearch "cohomology and Tor amplitude of closed exceptional inverse image and etale proetale comparison"`: eight hits, principally Ext-resolution comparisons and formal etaleness; none matches.
- `rg` on `lean/WeilConjectures` and `lean/Sheaf` for the item id, `etaleClosedOutputBounds`, and closed output/bounds: no matching declaration. The nearby `closedEtaleTransport_bounds` is a different theorem: its inputs are intrinsic pro-etale objects and it also identifies the pro-etale exceptional functor. It does not state this item's ordinary etale output theorem.
- Read the existing ordinary etale amplitude and Tor theorems, intrinsic interval,
  constructibility, comparison and Tor definitions. They supply the components,
  not this combined independent pair of etale-output assertions.
- `scompile.py --source Sheaf.SixFunctors.SfCategories`: `Module source unavailable`;
  its node already records that the module was deleted on 2026-10-20.

Validation: the module compiled separately in sandbox and library mode through
`scompile.py`, with no errors or warnings. The delivered final import visibility is
checked again by the prescribed dry run. No global build or direct repository edit
was run. All files written are in the authorized item sandbox.

## Dependency modules

`def-sf-categories`: lean-only repair under §1(B), using an existing declaration and
therefore introducing no module. Its recorded `Sheaf.SixFunctors.SfCategories` was
deleted, so it cannot be imported. The dependency is category notation, and the
ordinary ambient construction is exactly Mathlib `DerivedCategory`, specialized to
the existing module-sheaf category. The repaired existing record points to that
construction with an explanatory `lean.note`. Its other bounded, constructible,
Tor, interval and higher-coefficient notions remain the already existing
constructions cited in its statement; the consumer only needs the finite ordinary
ambient categories and explicitly uses those existing specializations. No source
or non-Lean node field changes, and no duplicate ambient category is written.

## Second reading by Q73

I reread the source node and final module clause by clause after compilation. This
is the dispatcher's single-worker recheck; no independent agent was started, in
accordance with the brief. The maintainer supplies the independent review.

The common assumptions match the fixed finite purity setting, finite-type
k-geometry, closed/open complementary ranges, nonnegative c, BOTH open-complement
clauses, bounded constructible etale input, and ordered integer bounds. The
ordinary right adjoint is fixed by the existing closed-ambient instance, and the
comparison object uses the existing canonical intrinsic comparison functor.
Conjunct (a) has only a cohomology premise and returns both etale bounded
constructibility/cohomological support and the intrinsic pro-etale interval.
Conjunct (b) has only a Tor premise beyond the common assumptions and returns
etale bounded constructibility/Tor support and intrinsic bounded constructibility
plus the full pro-etale Tor test. Unfolding the last predicate confirms universal
quantification over every degree-zero module sheaf and the exact inclusive output
interval. No etale-origin restriction, arbitrary adjoint, finite-Tor input for (a),
extra separatedness, or per-test rather than uniform interval was introduced.

The recheck retained the original intrinsic Tor predicate used by the finite-Tor
category instead of the underdetermined general-instance application. It also
repaired the deleted ambient-notation dependency to the existing ordinary derived
construction. All other node data are unchanged. The only delivered theorem has
its complete four-step source proof in its docstring and a whole `sorry` proof.
