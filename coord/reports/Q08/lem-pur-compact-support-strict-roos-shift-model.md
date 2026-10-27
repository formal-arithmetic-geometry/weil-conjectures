## Worker report

The module `Sheaf.SixFunctors.CompactSupportStrictRoosShiftModel` states
`WeilConjectures.IntegralSystemRealization.CompactSupportStrictRoos.compactSupportStrictRoosShiftModel`.
Its only theorem proof is `sorry`. All helper definitions contain real composites,
existing structures, or fully expanded propositions. There are no new nodes or
repaired dependency modules, and no changes to the natural-language statement.

Hypotheses and objects, clause by clause:

- `D : FiniteFieldDatum` is precisely the prime-power finite field and its specified
  algebraic closure. `l : ℕ`, `[Fact l.Prime]`, and `hl : l ≠ D.p` give the different
  coefficient prime. `E : Type u`, `[Field E]`, `[Algebra ℚ_[l] E]`, and
  `[FiniteDimensional ℚ_[l] E]` give the finite extension. The coefficient calculus
  uses its valuation ring and the quotient by powers of its maximal ideal. In a
  DVR this is the same ideal as the power of any chosen uniformizer; no generator
  affects the quotient maps, and none is added as extra data.
- `X W : Over (Spec (.of D.k))`, `f : X ⟶ W`, `c : Compactification f.left`, and
  `g : (expression f c).geometric` give the schemes and arrow over k, finite-type
  structure morphisms, separated finite-type f, and the fixed open/proper
  compactification. The geometry predicate is the existing conjunction of
  locally finite type and quasi-compactness. The quasi-compactness of c.i follows
  by cancellation against the proper factor, as in the existing interface.
- The existing `System l E W` is the ordinary unbounded derived category of
  strict semilinear module systems on the small pro-etale site. `calculus` retains
  the actual reduction/limit adjunction, its unit and counit, K-flat reduction
  models, and finite evaluation comparisons. `o : Operations l E` retains the
  simultaneous exact open and total right-derived proper models. `R : Realizations
  l E D o` is the supplied comparison with all its normalizations, not a newly
  chosen endpoint isomorphism.
- `allowed` is the existing domain of the unary compact-support expression on
  the singleton input family. It requires derived-complete constructibility of
  K, normalized reductions, compatible etale-origin witnesses, constructible
  positive levels, and common finite cohomological and Tor intervals for every
  intermediate system. Separate intervals for the finitely many intermediate
  systems are equivalent to taking a single interval containing them all.
- `systemOutput` is the actual composite reduction, J_j, S_p. `tower` is its
  exact termwise completed-coefficient restriction U_W, including maps. Thus
  `tower.obj K` is T_K localized as a strict tower, and `source` is precisely its
  total right-derived limit; these are the existing functors, not a replacement
  system in the category of derived diagrams.

Conclusions, clause by clause:

1. The first conjunct quantifies over all `m n : ℕ` and `h : n ≤ m`. The
   `pbcTowerTransition` of this actual tower, transported by `evaluation`, equals
   `compactSupportRestrictedTransition`. This existing map applies larger-level
   compact support to the K-flat-normalized quotient reduction, then the canonical
   coefficient-restriction comparison, then composition of restrictions along the
   completed projection. `evaluation` itself is the explicit composite of
   `coefficientRestrictedEvaluationIso`, `supportEvaluation`, and the calculus's
   `reductionEvaluation`; it is not free comparison data. Natural index n denotes
   exponent n+1, so all and only positive coefficient levels occur.
2. The second conjunct is naturality of the actual supplied c_(S_p J_j), for every
   integral morphism between allowed objects, using the full derived maps.
3. The third conjunct asserts closure of the allowed input domain under every
   integer shift and the equality
   `c(K[r]) ≫ integralShift = sourceShift ≫ c(K)[r]`.
   `sourceShifts` composes exactly reduction's adjunction mate, the exact open
   cochain shift, the proper mate, and the fixed right-derived-limit shift.
   The target uses `(integralShifts l E).compactSupport`, hence the actual
   completed open/proper composite. These are `CommShift ℤ` structures, whose
   zero/addition laws include negative integers and consequently inverse shifts.
   Thus the comparisons in the equation, rather than merely some isomorphic
   comparisons, carry the required integer coherence.
4. The fourth conjunct quantifies over every actual system complex `C` representing
   S_p J_j R(K), every normalized K-injective Roos bridge, and every termwise shifted
   representative `CShift`. The premises `hβ` fix the levelwise cochain shift;
   `hδ` is the existing two-summand signed cone formula. `RoosShiftEquation` is the
   expanded equality of the source total-limit shift and the localized shifted-cone
   map with the same bridges. It includes the actual representative identification
   `α`, the localization shift, and `completedTensorShiftRoosIso`, rather than a
   cone selected on derived objects. The existing cone formula is unsigned on one
   summand and multiplied by r.negOnePow on the shifted summand, then shifted by -1.
5. The fifth conjunct asserts invertibility of c and `RecordedIdentification`.
   This predicate composes c with the dependency's
   `sfQcqsCompactSupportRealization` to the recorded integral functor. Its reduction
   unit followed by `sfCompactSupportFiniteReductionIso` equals the actual total
   limit projection of T_K followed by its specified finite evaluation. Thus the
   identification is fixed on the actual compact-support projections, not only
   on object values. The necessary finite-type instances are extracted from g;
   the constructible input proof is extracted from hK. No extra hypotheses enter.
6. The last conjunct `StructuralMaps` is equality for every published
   `CanonicalPair` starting at compact support, including the proper/open
   compositors and their expression contexts. It uses the same R, the same c and
   the same actual system and integral maps, before evaluation. The definition
   uses the existing canonical-map relation without a private replacement.

The signed second tensor slot, although not used by this unary expression, is
retained unchanged in the imported operation-shift data and the canonical
expression contexts. The theorem docstring contains all four proof steps of the
node: quotient transitions; supplied realization and structural maps; K-injective
Roos shift; insertion-shift squares and integer coherence.

Dependency declarations read and used:

- `Sheaf.Paper.CoefDerivedSystemEvaluationCalculus`:
  `WeilConjectures.CoefficientDerivedSystemReductionModel` (actual reduction,
  adjunction, finite evaluations and K-flat model), `CoefficientDerivedSystemCalculus`,
  `coefficientDerivedSystemEvaluationCalculus`; accessed through the published
  `IntegralSystemRealization.calculus`. Its underlying sequence-site declarations
  provide `coefficientSequenceDerivedRestriction`, `coefficientSequenceLimit`,
  `coefficientRestrictedEvaluationIso`, and `coefficientConstantTowerProjection`.
- `Sheaf.SixFunctors.IntegralCompactificationSystemRealization`:
  `Realizations`, `Realizations.comparison`, `CanonicalPair`, and the canonical
  proper/open and structural-map normalization. Its imported
  `IntegralSystemExpressionDomain` supplies `Expression`, `domain`, `geometric`,
  `Good`, and the actual system/integral interpretations; `IntegralSystemOperations`
  supplies `Operations`, `supportEvaluation`, and `calculus`.
- `Sheaf.SixFunctors.IntegralOperationShiftData`: `reductionShift`,
  `systemOpenShift`, `systemPushShift`, `limitShift`, `integralShifts`,
  `restrictedTower`, `levelRestriction`, and `limitShift_roos`.
- `Sheaf.Paper.SfIntegralConstructible`: `WeilConjectures.sfIntegralConstructible`,
  used by the existing input domain and recorded integral realization.
- `Sheaf.Paper.FiniteTorAmplitudeSites`: recorded `finiteTorConstructible` family;
  its intrinsic Tor-amplitude notion is used by the domain's `LevelBounds`.
- `Sheaf.Paper.QcqsCompactSupportRealization`:
  `WeilConjectures.sfQcqsCompactSupportRealization`, the recorded natural
  identification with the integral compact-support functor. The completed
  proper/open presentation is `PurCompactSupport.image`.
- `Sheaf.SecSmoothPurity.IntrinsicCompactSupportRestriction`:
  `AlgebraicGeometry.ProEtale.intrinsicCompactSupportRestriction` and the retained
  `AlgebraicGeometry.Scheme.sfCompactSupportRestriction`. The latter uses the same
  sectionwise constant direct-image coordinates as `supportEvaluation` and is
  already part of `compactSupportRestrictedTransition`.
- `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients`:
  `CategoryTheory.ringedStrictTowerHomotopyLimitIndependentCoefficients`, the
  K-injective/right-derived strict-tower framework without exact-products assumptions.
- Proof imports are the recorded modules for `injectiveTowerRoosShifts`,
  `Recursion.integralRealizationRecursion`, `realizationAdjunctionInsertionShift`,
  and `SemilinearSections.Geometry.systemPushforwardRestrictionTransition`.
  They are plain imports; statement dependencies are public imports.

Edge cases checked from the displayed types and formulas: m=n is included by
`n ≤ m`; m>n is arbitrary, so direct and composite quotient maps are included;
exponent zero is excluded only because the node starts at positive exponents.
Shifts r=0, negative r, and successive inverse shifts all occur in ℤ and the
fixed `CommShift` data. The zero input and empty open/scheme have no nonempty
hypotheses. Identity open/proper factors are allowed. Equal X and W introduce no
extra separated structure-morphism assumption. Universes are explicit; small
pro-etale objects have universe u+1 and morphisms u as in the supplied framework.

Searches actually run using msearch.py:

- LeanFinder: "The strict compact support tower has quotient restriction transitions
  and its K-injective Roos shifted cone comparison equals the integral compact
  support shift". Eight hits, concerning CM5b replacements and generic bounded
  derived representatives; none states this result.
- Loogle: `CategoryTheory.Functor.CommShift`. Twelve hits for the existing shift
  structure and coherence API; reused those structures, no compact-support result.
- Mathlib grep: `Roos|compactSupport|commShift` in `Algebra/Homology`. Twenty-five
  generic cochain, homotopy-category and derived-category shift hits, no match.
- LeanSearch: "Derived inverse limit compact support strict coefficient tower
  canonical mapping cone shift". Eight mapping-cone and shift hits, including
  `CochainComplex.mappingCone.shiftIso`, no strict compact-support comparison.
- ripgrep of `lean/WeilConjectures` and `lean/Sheaf` for the node id,
  `compactSupportStrictRoos`, and compact/Roos/shift phrases found no existing
  declaration of this node. Broader searches found and reused the operation
  shifts, compact-support transition, realization, and Roos interfaces above.
  `dag/lean_names_upstream.json` has no declaration with the proposed name.

The current blueprint source was read at
`literature/blueprint/latest/blueprint/sec-six-functors/sk-thm-sf-compatibility/fix-prop-coherence.proof.md`.
The historical `sk-thm-sf-package` directory in the node's source record has moved;
the current proof retains the maps-used/coefficient-comparison sentence. As the node
already states, the shift obligation is an agent assembly, not a claim quoted from
the blueprint itself. No mathematical statement correction or disputed statement
was needed.

Validation: the prescribed server compiler passed both sandbox and actual library
module modes cleanly (14.6 s and 17.2 s); no warnings remain. In the review of the
first draft I made the Roos equality, recorded finite projections and structural-map
agreement explicit instead of leaving those clauses only in prose. Compiler warnings
were repaired by marking proof-only equation parameters and wrapping a long line.
The recorded-realization interface needed explicit X/Y arguments to disambiguate
its typeclass inference; no hypotheses or dependency declarations were altered.

## Second reading by Q08

Independent reading (maintainer cc reviewer) of the node, its eight stmt_deps and their
Lean records, and `lean/Sheaf/SixFunctors/CompactSupportStrictRoosShiftModel.lean` at
9fc5b3e0. The delivery's own section said that no second reader was started; this
section replaces it. Nothing in the Lean or the node record was changed.

Objects and hypotheses of the node, with the Lean rendering:

- k = F̄_q, ℓ ≠ p, E/Q_ℓ finite, R, t, A_n = R/t^n (n ≥ 1): `D : FiniteFieldDatum`,
  `hl : l ≠ D.p`, `E` with `[FiniteDimensional ℚ_[l] E]`; level n+1 is index `n`.
  OK, no uniformizer data is needed because only the ideal t^n enters.
- Finite-type k-schemes, small pro-étale sites, S_W, D(S_W), R_W ⊣ L_W with u, e:
  `X W : Over (Spec D.k)` with finite type in `g`; `System`, `Integral`, `calculus`
  (the recorded evaluation-calculus interface). OK.
- P_v, S_p, J_j, tensor with the integral counterparts: `o : Operations` (pinned
  evaluation, unit/counit and transition equations) and `R : Realizations`, the
  structure the realization node produces; every field is a normalization, so an
  arbitrary `R` is the specified c_V. OK.
- Allowed inputs and intermediate systems: `allowed = (expression f c).domain`, which
  contains `sfIntegralConstructible` of K, `Good` (normalized, `LevelBounds` with one
  cohomological and one Tor interval, `Nonempty Origins`) of R K, of J_j R K on the
  compactification and of S_p J_j R K. OK, no stronger assumption.
- f = p j with j quasi-compact open, p proper, f separated finite type:
  `c : Compactification f.left`, `g : (expression f c).geometric`. OK.
- Fixed shifts: `sourceShifts` = reduction mate, `systemOpenShift`, `systemPushShift`,
  `limitShift` of def-pur-integral-operation-shift-data; the target uses
  `(integralShifts l E).compactSupport`, the open/proper composite. OK.
- T_K = U_W S_p J_j R K: `tower = systemOutput ⋙ coefficientSequenceDerivedRestriction`;
  `systemOutput = reduction ⋙ shriek c.i ⋙ push c.g`. OK.

Conclusion clauses:

1. Transitions of T_K = R p_{*,m} j_! of the reduction map, then the coefficient
   restriction iso, then Res composition: conjunct 1, for all `n ≤ m`, with
   `compactSupportRestrictedTransition` (def-weil-compact-support-reduction-tower-data:
   `compactSupportReductionMap` (transpose of the pinned reduction unit), compact support
   at level m, `sfCompactSupportRestriction`, `compactSupportRestrictionComp`) and the
   explicit `evaluation` composite. Identities (m = n) and composites included. OK.
2. c_{S_pJ_j} identifies L S_pJ_jRK with the integral functor and its maps: conjunct 2
   (naturality), conjunct 5 (`IsIso`, and `RecordedIdentification`: c then
   `sfQcqsCompactSupportRealization` then the transpose of its finite-reduction iso equals
   the actual limit projection of T_K followed by `evaluation` — the transpose of the
   recorded `SfQcqsCompactSupportRealizationSpec`), conjunct 6 (`StructuralMaps`, every
   `CanonicalPair` starting at compact support, i.e. the realization's coherence field
   specialised). OK.
3. Source total-limit shift = completed integral compact-support shift, every r, with
   zero/addition/inverse laws and the proper/open composite: conjunct 3,
   c(K[r]) ≫ integral shift = source shift ≫ c(K)[r] with both shifts `CommShift ℤ`
   structures. The domain's shift-closure (`∃ hShift`) is true (all parts of `Good` and
   constructibility are iso-closed and shift-stable) and is needed to type c(K[r]). OK.
4. Roos model: conjunct 4 = the shifted-cone formula of `limitShift_roos` on every strict
   representative C, every normalized Roos bridge ρ and every termwise shifted
   representative with pinned β, δ. The premise ε : Q C ≅ S_pJ_jRK only records that C
   represents T_K; the equation does not need it. OK (it is the node's "explicitly
   including S_pJ_jRK").
5. "No selection of a cone": none is chosen; δ is pinned by `completedTensorShiftConeFormula`.

Edge cases: m = n; r = 0, r < 0; K = 0 (domain has no nonemptiness condition); j = id,
p = id; X empty. Universes: E and schemes in u, as in the dependency interfaces.

Searches: as in the worker report; also rg of lean/Sheaf for `compactSupportStrictRoos`,
`RoosShiftEquation`, `compactSupportRestrictedTransition` users: no existing statement of
this node.

Advisories (not faults): the statement uses plain defs of nodes reached only through the
cited deps (def-weil-compact-support-reduction-tower-data, def-weil-pbc-bounded-constructible-tower,
def-coef-ringed-sequence-site, def-sf-integral-system-operations,
def-sf-integral-system-expression-domain, def-weil-compact-support-finite-action,
def-trf-integral-comparison-realization-models), and the cone formula defs owned by
lem-sf-completed-tensor-shift-right through the cited `limitShift_roos`; the
unit of `derivedScalarExtensionRestrictionAdjunction.choose` is the upstream convention
(pinned on K-flat representatives).

Changed by this reading: only this report section.
