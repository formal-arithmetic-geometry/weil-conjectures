## Worker report

Retained and checked the saved stage-2 packet. `Sheaf.Paper.FiniteTorStability`
states the seven clauses of `thm-sf-ctf-stability` as a family of named theorems;
all postponed theorem proofs are `sorry`. The auxiliary definitions specify actual
functors, restrictions, and canonical comparison maps, rather than adding arbitrary
six-functor data as hypotheses. The source is the current main-20261015 blueprint,
sec-six-functors/sk-thm-sf-kunneth-verdier/thm-sf-ctf-stability.md, together with the
current node's explicit nonnegative dimension bounds and positive coefficient levels.
The resolved stage-1 repair note requires the statement to remain unchanged; it does.

Hypotheses and clauses:

- The global datum is `D : FiniteFieldDatum`; `[Fact l.Prime]` and `hl : l ≠ D.p`
  render the coefficient prime. `E`, its field/algebra instances and
  `[FiniteDimensional (Padic l) E]` render the finite extension. Level `n + 1`
  ranges over exactly all positive integers, including exponent one and ramified E.
- `X Y : Over (Spec (.of D.k))` and the separated, locally finite-type and
  quasi-compact structure morphisms render separated finite-type k-schemes.
  The same properties on `f.left` render the morphism hypotheses. The integral
  and common-stage clauses use the equivalent `Over` and `IsOver` instances.
- `finiteTorConstructible` is the recorded bounded constructibility/finite Tor
  predicate. `HasProEtaleTorAmplitude` supplies the actual test-sheaf Tor interval;
  `IsFiniteCoefficientSitePerfect` is required only for the elementary Hom formula.
- (i): the first conjunct of `finiteTor_stability` uses `finiteDerivedPullback`.
- (ii): its second conjunct uses `finiteIntrinsicDerivedTensor` and the interval
  `[a+c,b+d]`. Its third conjunct uses `finiteIntrinsicDerivedInternalHom`, with
  general preservation and `[c-b-2m,d-a+2m]` for `m : ℕ` and
  `topologicalKrullDim X ≤ m`. Only the site-perfect implication supplies the
  coefficient-dual tensor isomorphism and sharper interval `[c-b,d-a]`.
  `finiteTor_stability_origin` states the literal affine-line origin example:
  both inputs have Tor interval `[0,0]`, their Hom is the minus-one twist shifted
  by -2, and H² is nonzero.
- (iii): the fourth conjunct uses `proEtaleConstantDerivedDirectImage` and
  `[a,b+2d]` for a supplied natural dimension bound d.
- (iv): the last conjunct uses `sfIntrinsicCompactSupport` at every
  compactification c. The restricted support functor is a literal full-subcategory
  lift of this candidate; the recorded coherence theorem supplies independence.
- (v): `finiteTor_stability_exceptional_verdier` gives preservation for the
  specified `ProEtale.sfFiniteExceptional`, its `D_X f* D_Y` formula and interval
  `[a-2dX,b+2dY]`. `finiteTor_stability_constructible_adjunction` states the
  constructible adjunction and natural functor formula, fixing maps as well as objects.
- (vi): `sfStabilityFiniteVerdier` is internal Hom into the exceptional image of
  the coefficient unit along the structure map. The recorded
  `FiniteProEtaleVerdierBiduality` asserts the canonical evaluation-transpose
  biduality; `finiteTor_stability_verdier_intrinsic` asserts the exact
  anti-equivalence in the intrinsic category used here.
- (vii), finite: `finiteTor_stability_quotients` uses every `h : n ≤ m`, including
  equality, and the published reduction of tensor and general Hom. It states
  `CoefficientEvaluationCompatible` and invertibility of the explicitly constructed
  Verdier and compact-support coefficient maps.
  `finiteTor_stability_geometric_quotients` gives the canonical pullback,
  ordinary direct image and exceptional coefficient comparisons, including the
  exceptional mate's counit identity (hence its adjunction normalization).
- (vii), integral: `finiteTor_stability_integral_hom` states equality of
  `sfIntegralConstructible` and `finiteTorConstructibleIntegral`, preservation by
  general internal Hom, and all canonical finite Hom reductions.
  `finiteTor_stability_integral_verdier` and its reduction theorem supply integral
  exact duality and the evaluation-defined finite comparison.
  `finiteTor_stability_integral_images` states exceptional preservation;
  `finiteTor_stability_integral_adjunction` identifies the duality composite with
  the right adjoint of coherent-limit compact support and states its finite reductions.
- (vii), fields: `finiteTor_stability_rational` gives the operations and exact
  Verdier anti-equivalences at raw rational localization, together with their
  localization comparisons, the exceptional adjunction and duality formula.
  `finiteTor_stability_algebraicClosure` gives them in the actual common-stage
  category, with restriction comparisons at every finite coefficient field.
  The Hom-pair predicates are top: the general Hom applies to every pair.
  No unrestricted unbounded pro-etale exceptional adjunction is assumed.

Dependency declarations used (the twelve original statement dependencies):

- `def-weil-finite-field-fiber`: `Sheaf.Paper.FiniteFieldFiber`, `WeilConjectures.FiniteFieldDatum`.
- `def-weil-finite-tor-amplitude`: `Sheaf.Paper.FiniteTorAmplitude`, `WeilConjectures.finiteTorConstructible`.
- `def-weil-finite-torsion-constructibility`: `Sheaf.Paper.IntrinsicFiniteTorsionConstructibility`, `AlgebraicGeometry.Scheme.intrinsicFiniteTorsionConstructible`.
- `def-weil-scheme-morphism-properties`: convention node; Mathlib `Scheme`,
  `IsSeparated`, `LocallyOfFiniteType`, and `QuasiCompact` are used directly.
- `def-weil-site-perfect-complex`: `Sheaf.Paper.SitePerfectComplex`, `WeilConjectures.IsFiniteCoefficientSitePerfect`.
- `def-weil-derived-complete-integral-detailed`: `Sheaf.Paper.SfIntegralConstructible`, `WeilConjectures.sfIntegralConstructible`.
- `def-weil-exceptional-inverse-image`: existing `WeilConjectures.ConstructibleExceptionalCoefficients.System` and its recorded stage/system declarations in `Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients`; `AlgebraicGeometry.ProEtale.sfFiniteExceptionalAt` is retained from `Sheaf.AlgebraicGeometry.FixedFiniteExceptionalAt`.
- `def-compact-support-direct-image-detailed`: `Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport`, `AlgebraicGeometry.Scheme.sfIntrinsicCompactSupport`.
- `def-kun-topological-krull-dimension`: `Mathlib.Topology.KrullDimension`, `topologicalKrullDim`.
- `def-weil-l-adic-coefficient-extension`: `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`, `Padic.finite_coefficientExtensionRing`.
- `def-weil-constructible-intervals`: `Sheaf.AlgebraicGeometry.IntrinsicConstructibleIntervals`, `WeilConjectures.intrinsicConstructibleIntervalCategory`.
- `def-coefficient-twists-detailed`: the current record is
  `Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted`,
  `WeilConjectures.sfQbarTwistingFunctor`; its retained public `Sheaf.Paper.IntrinsicCoefficientTwists` interface supplies the
  finite, integral, rational and intrinsic common-stage twists used here, including
  `WeilConjectures.intrinsicQbarComplexTwistFunctor`.

The scheme-properties node is a convention: the corresponding Mathlib scheme
properties are used directly. The finite and integral predicates contain bounded
constructibility, so no separate choice of an interval category is imposed.
The intrinsic and fixed-scalar presentations are related by the already published
constant-ring realization functors; the packet does not introduce a second category.

Edge cases checked: empty X or Y (dimension is bottom and zero is an admissible
natural bound); zero complexes; ordered or impossible Tor intervals (the recorded
Tor predicate includes order); exponent one; all quotient identities n=m; ramified
finite extensions (no restriction on the ramification index in the theorem);
site-perfectness is not imposed for general Hom; arbitrary finite common stages
and arbitrary algebraic closure universe v are retained. Integral uniform bounds
are required at all positive levels by the recorded predicates, not inferred from
unrelated levelwise models. No statement correction or disputed mathematical
statement is claimed.

Searches retained from the saved search log:

- msearch grep, `constructibleFiniteTor_preservation|finiteTorConstructible|preservationMatrix`:
  zero Mathlib matches.
- msearch loogle, `ObjectProperty, Functor, DerivedCategory`: zero matches;
  the service did not recognize ObjectProperty.
- msearch leanfinder, “The six derived operations preserve bounded constructible
  complexes of finite Tor amplitude over finite coefficient rings, and commute
  with coefficient reduction”: eight cohomological truncation results, no match.
- msearch leansearch, “six operations preserve bounded constructible finite Tor
  amplitude complexes and commute with reduction”: eight general exactness and
  filtered-colimit results, no six-operation theorem.

## Dependency modules

The three retained dependency repairs were accepted by the independent review of
bb8bf88aadda. Their node copies change only `lean`; their mathematical statements
are unchanged.

- `lem-sfb-unbounded-site-comparison`, module
  `Sheaf.AlgebraicGeometry.UnboundedSiteComparison`: the retired
  `ComparisonGlobalCohomology` import is replaced by
  `ComparisonGlobalCohomologyFiniteNormalized`. The unbounded exact,
  fully faithful, coproduct-preserving comparison is unchanged.
- `prop-compactification-coherence-detailed`, module
  `Sheaf.Paper.CompactificationCoherence`: retired pro-etale imports are replaced
  by their finite-coefficient counterparts and the normalized finite global
  cohomology comparison. The witnessed-origin candidates, refinement maps and
  identity/composition/common-refinement coherence statements are unchanged.
- `prop-sf-localization-all-stages`, module `Sheaf.Paper.SfLocalizationAllStages`:
  the original repeated derived unit equations exceeded the per-file limit.
  `SfLocalizationUnitCompatibility` names their exact commuting equation and
  is instantiated by the same ambient adjunctions and comparison isomorphisms.
  The transparency setting affects elaboration only. Two further transparent
  predicates, `SfLocalizationScalarUnitCompatibility` and
  `SfLocalizationScalarCounitCompatibility`, share the six rational and
  common-stage unit/counit equations. Their functors, adjunctions, natural
  isomorphisms and universal quantification are unchanged. All finite/integral/
  rational/common-stage localization conclusions and hypotheses are retained.

`lem-weil-delta-restriction` and its module are byte-for-byte the current shared
versions. They are retained in the saved packet solely as restored files and
introduce no delivery delta. The exceptional inverse-image node is also exactly
the current shared node, including its reviewed System record and 43 declarations;
no exceptional-interface replacement is delivered.

## Second reading by Q116

This is the resumed worker's self-check, with the current node, the complete
987-line `FiniteTorStability.lean`, the current main-20261015 blueprint statement,
the dependency records, and the three retained dependency diffs open. Independent
review remains with the maintainer. The following checks cover each hypothesis
and clause, rather than inferring correctness from compilation.

- Standing hypotheses: `FiniteFieldDatum.{u}` supplies the specified finite field
  and algebraic closure; `l : ℕ`, `[Fact l.Prime]`, `hl : l ≠ D.p` supply the
  coefficient prime. `E : Type u`, `[Field E]`, `[Algebra (Padic l) E]` and
  `[FiniteDimensional (Padic l) E]` supply precisely the finite extension.
  `Padic.coefficientExtensionRing l E (n + 1)` uses its recorded valuation ring
  and uniformizer. Every positive level occurs; no unramifiedness is assumed.
- Scheme and morphism hypotheses: the two `Over (Spec (.of D.k))` objects and
  `[IsSeparated]`, `[LocallyOfFiniteType]`, `[QuasiCompact]` on their structure
  maps and on `f.left` express separated finite-type schemes and morphisms.
  The later `Scheme.Over` and `f.IsOver` presentations retain the same base.
  Compactness and quasi-separatedness needed for Nagata are derived from these
  hypotheses, rather than extra assumptions.
- Clause (i): the first conjunct of `finiteTor_stability` maps every
  `finiteTorConstructible` input by `finiteDerivedPullback` into the target
  `finiteTorConstructible` predicate. There is no site-perfect hypothesis.
- Clause (ii): the next two conjuncts give tensor and general internal Hom
  preservation for every constructible finite-Tor pair. The tensor interval is
  `(a + c, b + d)`. For `m : ℕ` bounding `topologicalKrullDim`, general Hom
  has `(c - b - 2*m, d - a + 2*m)`. Only the implication from
  `IsFiniteCoefficientSitePerfect` contains the coefficient-unit dual/tensor
  isomorphism and `(c - b, d - a)`. In `sfStabilityOriginConclusions` the
  origin is evaluation at zero on the literal one-variable polynomial spectrum;
  both inputs have `(0,0)`, the Hom is the supported minus-one twist shifted
  by `-2`, and `¬ IsZero` of homology in degree `2` asserts actual nonvanishing.
- Clause (iii): the fourth conjunct uses the recorded constant-ring derived
  direct image and outputs `(a, b + 2*d)` for every natural dimension bound `d`.
- Clause (iv): the last conjunct quantifies over every `c : Compactification
  f.left`. All three compact-support expressions in the file, including its
  full-subcategory restriction and coefficient mate, use the recorded
  `sfIntrinsicCompactSupport c A`. I checked its body: exact extension by zero
  followed by `proEtaleConstantDerivedDirectImage c.g A`. It is the same formula
  required by the node. No `sfAmbientCompactSupportCandidate` remains.
- Clause (v): `finiteTor_stability_exceptional_verdier` preserves the specified
  `ProEtale.sfFiniteExceptional`, identifies its value with `D_X f* D_Y`, and
  gives `(a - 2*dX, b + 2*dY)`. Both dimensions are natural upper bounds,
  so empty schemes admit zero. `finiteTor_stability_constructible_adjunction`
  supplies the restricted compact-support adjunction and the natural functor
  formula on maps as well as objects. The restored System record is preserved;
  its finite interfaces remain available among its recorded declarations.
- Clause (vi): `sfStabilityFiniteVerdier` is Hom into the exceptional image of
  the unit along the structure map. `FiniteProEtaleVerdierBiduality` retains
  the canonical evaluation-transpose biduality, and the intrinsic theorem
  asserts `IsExactAntiEquivalenceOn` for this very functor and predicate.
- Clause (vii), finite: quotient theorems quantify over every `h : n ≤ m`,
  including identity. They use canonical tensor/Hom evaluation comparisons,
  direct-image and exceptional maps, the compact-support scalar mate and the
  reduced dualizing map. `CoefficientEvaluationCompatible` retains evaluation
  and composition; the exceptional counit identity fixes its adjunction
  normalization. `sfStabilityQuotientRestrictionEquality` identifies the strict
  tower quotient with the direct quotient before forming the support mate.
- Clause (vii), integral: `finiteTor_stability_integral_hom` equates the
  recorded complete bounded constructible and finite-Tor predicates and gives
  general Hom preservation and every finite comparison. The integral Verdier
  theorems give exact duality and evaluation-defined finite reductions. The
  exceptional composite uses integral duality and completed pullback;
  `finiteTor_stability_integral_adjunction` identifies it as right adjoint of
  the coherent-limit compact-support functor and gives all finite reductions.
- Clause (vii), fields: the rational predicate uses the specified raw
  localization and identifies its operations with the integral ones by natural
  localization comparisons. The algebraic-closure predicate uses the recorded
  common-stage category, quantifies over all finite coefficient fields, and
  gives their restriction comparisons. Both include exact duality, exceptional
  adjunction and the duality formula; their Hom-pair predicates equal top.
  The algebraic closure retains its independent universe `v`.

I also reread the retained dependency diffs. UnboundedSiteComparison and
CompactificationCoherence change imports only. The three coefficient pullback
helpers remain solely in the published `Sheaf.Paper.PurityRelativeKummer` module;
no replacement or duplicate module is delivered. The stability signatures do not
use these helpers, and relative Kummer is not a direct statement or proof dependency.
Its unused direct import was removed after the full dry run exposed a legacy
global-cohomology import in that module. The localization helper
expands to the previous unit equation with exactly the same comparisons. All
retained node copies retain their non-lean fields. No new mathematical notion or
statement correction is introduced.

The saved packet already implements R1--R3: the reviewed exceptional record and
full DeltaRestriction record/module match the shared versions; the rejected
finite-type exceptional, purity-chart and general-admissibility files are absent;
the three rejected imports are absent; and the canonical compact-support
identifier is used throughout. For R4, I corrected the report's compact-support
dependency from the old module/declaration to its current recorded intrinsic
interface, removed the obsolete DeltaRestriction repair claim and historical
validation narrative, and supplied this full reading.

Edge cases checked again: empty source or target with dimension bound zero;
zero objects; ordered Tor intervals (ordering is part of the Tor predicate);
level one and ramified coefficient extensions; identity quotients; arbitrary
compactifications and finite coefficient stages; uniform integral bounds at
all positive levels; and general Hom without site-perfectness. No mismatch in
the accepted seven-clause statement was found, and its text is unchanged.

## Validation

On this repair retry, inspected the retained report and ran the required saved-packet
`deliver2.py Q116 thm-sf-ctf-stability --no-push` before editing. Both the local
compiler and server confirmation timed out on `Sheaf.Paper.SfLocalizationAllStages`.
The remaining repair therefore addresses that concrete diagnostic while retaining
the existing stability statements and the import reuse required by return L.

The return-L self-check opened `PurityRelativeKummer.lean` and verified the full
signatures and bodies of `PurityFiniteSetting.constantPullback`, `twistPullback`,
and `derivedCoefficientPullback`. The packet uses no private copies of these constructions and contains no active `PurityAffineLineDatum.lean` or `PurityRelativeKummer.lean`
replacement. Backup files are outside the delivery set. The three duplicate
constructions reported at ba4e39fb85e6 are therefore not delivered or renamed.

Read the current main-20261015 blueprint theorem and all 987 lines of the retained
stability module. The clause mapping in the second reading remains applicable.
Compared the saved nodes with the current shared nodes: only `lean` changes in
the item and three dependency records; the restored DeltaRestriction and exceptional
records are identical to their current shared versions. The stage-1 repair note
is resolved and requires the unchanged statement.

The timeout repair was guided by `trace.profiler` in a temporary diagnostic copy:
`SfRationalLocalization` and `SfLocalizationStageComparison` accounted for repeated
unit/counit elaboration. Factored their six equations into
`SfLocalizationScalarUnitCompatibility` and
`SfLocalizationScalarCounitCompatibility`, both in the owning localization module
and its `lean.declarations`. For the open unit the arguments are `FX`, `FU`,
`S₀.openAdjunction`, `S₁.openAdjunction`, `open_pull`, `open_push`; for the closed
exceptional unit/counit they are `FZ`, `FX`, the two exceptional adjunctions,
`closed_push`, `exceptional`. The rational record instantiates the same forms with
its actual localization functors and integral/field adjunctions. Unfolding gives
exactly each previous equation, including every object binder and arrow order.
The helpers contain actual formulas, no postponed data or new theorem.
Diagnostic checkpoints and profiler options were removed before final validation.

The full dry run passed the repaired localization module, then failed in the
private overlay for legacy `ComparisonGlobalCohomology`, reached only by the
unused direct `PurityRelativeKummer` import. The wrapper classified the conflicting
legacy/finite lower-shriek declarations as a stale-live-build infrastructure error.
Checked the complete current statement/proof dependency list: relative Kummer is
not a direct dependency, and no stability signature or definition uses its helpers.
Removed this unused import, keeping all existing constructions at their published
owner. This avoids that legacy import without changing any Lean statement or
adding another dependency module. The two required global-comparison dependencies
already import `ComparisonGlobalCohomologyFiniteNormalized` in this packet.

Final dry run on 2026-10-18: `OK (dry run): commit ef0401fcab passes the
preflight and compiles; nothing pushed`. The wrapper's authoritative server
confirmation accepted all files after a private-overlay timeout. The staged delta
contains four Lean modules (the main statement and three dependency repairs),
four changed node records, and the report. The restored exceptional node and
DeltaRestriction node/module produce no delta. No active duplicate purity module
is delivered. An exact-name ripgrep search over Mathlib, upstream WeilConjectures
and shared Sheaf sources found no existing declarations with either new scalar
compatibility helper name. The final push uses these same Lean files and records.


## Resumed self-check, 2026-10-18

The first prescribed saved-packet dry run in this resumed session returned
`OK (dry run): commit f4caadc2ad passes the preflight and compiles; nothing pushed`.
Following the repair brief, retained every Lean file. Reread the complete 987-line
stability module against the current node and main-20261015 blueprint; the existing
hypothesis-by-hypothesis and clause-by-clause reading above still applies. Compared
the sandbox nodes and modules with the current shared base: the four changed node
records change only `lean`, the two restored node records are identical to the base,
and the three dependency module differences are exactly those described above.

In particular, checked each localization helper against the original displayed
unit/counit equation. Expanding its body retains the original quantified object,
adjunctions, comparison isomorphisms and composition order, for the finite units,
rational localization, and common-stage comparisons. No hypothesis, normalization,
coefficient stage or dimension bound changes. The wrapper compiled every packet
file and checked the existing declaration probes, under the prescribed per-file
limit. No diagnostic options or scratch modules enter the delivery. Only this
resumed validation record and the corrected line count were added after that dry run;
the delivery wrapper repeats compilation and preflight before pushing.
