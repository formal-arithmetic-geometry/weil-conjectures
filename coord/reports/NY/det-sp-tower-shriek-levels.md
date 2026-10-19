## Worker report

This delivery states `AlgebraicGeometry.ProEtale.SpTowerShriek.tower_shriek_levels`
in `Sheaf.Paper.SmoothPurityTowerShriekLevels`. Its existential conclusion supplies
`Base`, `Operations`, and `OpenExchange` satisfying `Laws`. These are conclusions,
not additional hypotheses. All helpers are parts of this node's specified operations;
there are no new independent notions or nodes. The sole postponed proof is the named
main theorem, whose docstring gives all six steps of the DAG proof.

The objects are the actual varying-ring systems. `S` and `D` abbreviate the published
`SemilinearSections.Systems` and its ordinary unbounded derived category on the small
pro-etale sequence site. `Base.realization`, `sections`, `restrictions`, and `morphisms`
identify this presentation with the recorded `spCoefficientTowers`, retaining every
section and semilinear transition. The additive equivalence transfers the abelian and
derived statements; this is not a diagram category of derived objects. Schemes and E
have universe u, pro-etale objects have universe u+1 and arrows universe u. The explicit
smallness instances preserve those universes.

Hypotheses and coefficient conventions:

* `l : ℕ`, `[Fact l.Prime]`, `E : Type u`, `[Field E]`, `[Algebra (Padic l) E]`,
  `[FiniteDimensional (Padic l) E]` are the prime and finite coefficient extension.
  The valuation ring and uniformizer are the dependency's existing definitions.
* Index n in the file is the paper's positive exponent n+1, as in the recorded tower.
  `R l E n` is O_E/(ell)^(n+1); `B` is the recorded constant ring sheaf and `tau`
  is its actual adjacent quotient homomorphism. No zero-exponent level is introduced.
* `Base.ramification`, `ramification_positive`, `ramificationUnit`, and
  `ramification_eq` express ell = unit times the specified uniformizer to a positive
  power. `Base.ideals` is the equality of the actual defining ideals at every level.
  `quotientTransport` is equality elimination on those ideals, induced by the identity
  of O_E; it makes no arbitrary choice of an equivalence.
* `GoodLevel` applies the dependency's `finiteTorConstructible` at exponent e(n+1)
  after that exact quotient identification. It thus retains bounded constructibility
  AND finite Tor amplitude, rather than defining a replacement predicate.
* `Origin` retains a fixed-module D+ object, its specified canonical intrinsic
  realization isomorphism, and the dependency's `FixedEtaleOriginWitness`. The
  hypotheses supply a function of n with values in this witness type. There is no
  compatibility equation between witnesses at distinct levels.

Clause 1:

* A `Compactification f` is the recorded c=(j,p); its `i`, `g`, and `comm` are used.
* `Open.extension` is exact and additive on actual systems; `openD` is its termwise
  derived functor. Its ordinary adjunction is fixed by the finite unit and counit
  equations, and its derived unit and counit are their exact termwise localizations.
* `Geometry.push` is the actual generic system direct image, in fixed constant-ring
  coordinates. `push` is its total right derived functor and `adjunction` is the
  canonical derived ordinary adjunction, with `derivedAdjunction_eq` fixing the
  generic derived model as well.
* `F` is literally `openD c.i ⋙ push c.g`. `Fcomparison` is a natural isomorphism
  formed by composing the open and proper evaluation comparisons and associators.
  Its target `finiteF` is the finite `j_!` followed by finite `Rp_*` in the identical
  constant-ring coordinates. `Laws.bounded` preserves the D+ domain. The unbounded
  total operations have exactly this restriction, without a separate chosen functor.

Clause 2, existence and evaluation of specified operations:

* `Base.calculus` is the existing signed K-flat calculus. `tensor` is its actual
  ringed-sequence-site derived tensor. Its `tensorEvaluation`, `tensorEvaluationModel`,
  `tensorEvaluationModel_ordinary`, `scalar`, `reduction`, and `reduction_cocycle` retain
  finite tensors and the derived quotient-transition formula; no flatness of a
  quotient map, cartesian input tower, completed tensor, or condensed identification
  is imposed. These assertions apply to every pair of input towers, hence in
  particular to any specified coefficient-twist tower on an ell-invertible scheme.
  Such a specified tower is an actual system with its quotient transitions, not a
  family of twist objects in separate derived categories. The dependency's signed
  finite twists are publicly imported; no twist is redefined or replaced by a unit.
* `Geometry.generic`, its HEq transport fields, `transitionFormula`, and
  `pullTransitionFormula` retain the actual geometric system functors, the precise
  coefficient-transition counit mates, and the same target tensor. The generic
  signed representative and pure-tensor normalizations are retained in full.
* `Geometry.projectionEvaluation` retains the generic finite counit-transpose
  evaluation equation. `Operations.comp_termwise` makes composition the localization
  of an actual ordinary natural isomorphism; `comp_evaluation` fixes its finite
  canonical constant-section composition. Thus it is not a putative lift of a family
  of derived composition maps.
* `Operations.openTensor_mate` fixes the inverse open tensor comparison by its open
  adjoint transpose. Its naturality and finite evaluation follow from that same
  formula, the termwise normalized open adjunction, and `Geometry.tensorPullback`.
* `projection` is written as the proper counit-tensor transpose, followed by proper
  image of the specified open tensor comparison, and the canonical pullback
  composition with c.comm. It is defined on all unbounded input objects before any
  witnesses are tested. Every factor evaluates to the identical finite specified
  projection word by the preceding normalizations, so its evaluation is the finite
  compactification projection, with the canonical coefficient-coordinate transports.
* `square` uses the specified composition isomorphisms and the actual commuting
  equation. `openMate` is the specified open-adjunction transpose; `OpenExchange.mate`
  fixes the inverse open base-change isomorphism to that map. `exchange` uses the
  dependency's `compactificationExchangeFromData`, hence applies the proper unit,
  square comparison, proper counit, and then proper image of open base change.
  The normalized adjunctions and composition comparisons make evaluation the same
  finite compact-support exchange word. No equation of arbitrary derived maps is
  inferred from their evaluations.

Clause 2(a): `Laws.projection_iso` quantifies `FiniteFieldDatum k`, l != k.p,
objects X,Y of Over(Spec k.k), separated finite-type structure morphisms, the
k-morphism f and its chosen compactification, and K,L in the actual D+ tower
categories. BOTH inputs have independently specified origins and `GoodLevel` at
EVERY level. The conclusion is `IsIso (projection ... K.obj L.obj)`. No uniform Tor
interval is added, and the tensor formula is formed in D, not forced back into D+.

Clause 2(b): `Laws.exchange_iso` quantifies an arbitrary cartesian square, a
separated finite-type f, arbitrary g, and c. `c.ofIsPullback sq` is exactly the
recorded base-changed compactification; the proper and open squares used in
`exchange` are its actual pullback squares. The input is D+ with independent
specified origins at every level. The conclusion is invertibility of this exact
exchange component. No finite-type, quasi-compactness, or origin condition is
added to g.

Clause 2(c): `Laws.localization` supplies `LocalizationData` for every closed i,
quasi-compact open a, and exact complementary-range equation. It asserts exactness
of ordinary closed direct image. The triangle uses the actual open derived counit
and the exact termwise localization of the ordinary closed unit. Its third arrow
has target the shift by 1 of a_! a^-1 C. The SAME triangle, with its connecting
arrow, is sent to a finite distinguished triangle by every exact evaluation.
Ordinary pull and push evaluations and the normalized level adjunction identify
its first two maps with the finite open counit and closed unit. The proof docstring
constructs this from one strict representative and one degreewise short exact
sequence, not from unrelated level triangles. Tensor evaluation applies also to
each specified finite-Tate-twist tower with its quotient transitions; no completed
coefficient object occurs in the formula.

Clause 3: `Laws.detects` quantifies every actual morphism of the UNBOUNDED `D` and
asserts `IsIso v ↔ ∀ n, IsIso ((Ev ... n).map v)`. It asserts neither faithfulness
nor existence of maps realizing arbitrary level families. The proof is the cone
argument with componentwise cohomology.

Dependency declarations used (module; declaration):

* `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` (via tower imports);
  `Padic.coefficientExtensionIntegers`, `coefficientExtensionUniformizer`,
  `coefficientExtensionIdeal`, `coefficientExtensionRing`,
  `finite_coefficientExtensionRing`.
* `Sheaf.Paper.SmoothPurityCoefficientTowersAbelian`;
  `ProEtale.spCoefficientCommRings`, `spCoefficientTowers`,
  `SpCoefficientTowersAbelian`, `sp_coefficient_towers_abelian`.
* `WeilConjectures.Compactification.Refinement` and `.BaseChange`;
  `Compactification`, `.ofIsPullback`, `.isPullback_i_ofIsPullback`.
* `Sheaf.Paper.FiniteFieldFiber`; `WeilConjectures.FiniteFieldDatum`.
* `Sheaf.Paper.FiniteTorAmplitude`; `WeilConjectures.finiteTorConstructible`.
* `Sheaf.AlgebraicGeometry.FixedEtaleOriginWitness`;
  `Scheme.FixedEtaleOriginWitness`.
* `Sheaf.Paper.PbcCoefficientTwists`, publicly retaining
  `CoefficientTwistsDetailed`/`IntrinsicCoefficientTwists` and their finite twists.
* `Sheaf.Paper.SemilinearDerivedSections`; `SemilinearSections.Systems`, `DS`,
  `evaluation`, `e`, `Data`, `Geometry`, `TransitionFormula`,
  `PullTransitionFormula`, `ProjectionEvaluation`, `semilinearDerivedSections`.
* `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`;
  `proEtaleConstantRingPullback`, `proEtaleConstantRingPushforward`,
  `proEtaleConstantRingAdjunction`, `proEtaleConstantRingDerivedPullback`.
* `Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZero` and `...Exact`;
  `sfIntrinsicModuleEquivalence`, `sfIntrinsicExtensionByZero`, exactness instances.
* `Sheaf.AlgebraicGeometry.ProEtaleConstantOpenSquareExchange`;
  `openSquarePullbackModel` and the reexported `sfIntrinsicOpenAdjunction`.
* `Sheaf.AlgebraicGeometry.ProEtaleConstantRingPullbackComparison`;
  `proEtaleConstantRingPullbackComposition`.
* `Sheaf.Paper.ExchangeProjectionSuppliedDomains`;
  `SuppliedExchangeProjection.compactificationExchangeFromData`; the projection
  definition implements its counit-transpose/open-comparison prescription directly
  in the published uncurried tensor coordinates.
* All recorded, available proof modules are imported non-publicly for stage 3,
  including finite projection, finite base change, ringed open--closed, exact-functor
  derivation and the Mathlib SES triangle. The currently unstated
  det-sp-tower-injective-components is a proof dependency, not an object needed to
  type the statement; no fictitious declaration is substituted for it.

Edge cases checked: n=0 means exponent one; e>=1 covers ramified extensions;
empty schemes and zero complexes remain admitted; no nonzero/rank hypothesis on
inputs; negative and zero Tate twists are included because evaluation is stated
for the actual general tensor; no flatness of R_(n+1)->R_n; arbitrarily growing
level Tor intervals; unbounded cones and morphisms; identity and arbitrary
non-finite-type base maps; empty or full open complement; distinct site object
and morphism universes. No statement correction or disputed statement remains.

Searches made for an existing statement:

* `msearch.py ... leanfinder "derived compactly supported image of varying coefficient
  towers computed levelwise projection base change localization"`: eight generic
  derived-functor/Ext/local-cohomology hits; no varying-ring compact-support theorem.
* `msearch.py ... loogle "CategoryTheory.IsIso, CategoryTheory.Functor"`: twelve
  generic functor-isomorphism results; no matching statement.
* `msearch.py ... grep "tower.*shriek|shriek.*tower|system.*compact|compact.*system"
  CategoryTheory`: two cofiltered-system/topology hits, no match.
* `rg` in upstream WeilConjectures, shared lean/Sheaf and dag/lean_names_upstream.json
  for `det-sp-tower-shriek-levels|sp_tower_shriek|SpTowerShriek`: no existing item.
  Broader tower/compact-support searches found the fixed-coefficient interfaces and
  the published semilinear calculus, which are used rather than duplicated.

## Second reading by NY

The dispatcher explicitly forbids other agents and assigns the independent reading
to the maintainer. This is a self-audit, not a claim of an independent second reader.
With the node and module open, I checked each numbered clause and each domain as
mapped above. The audit added the actual ramification-ideal transport so that
GoodLevel uses the recorded predicate; retained the witnesses as data rather than
mere Nonempty hypotheses; fixed geometric coefficient-transition formulas and the
canonical derived adjunction; and ensured that open tensor and exchange comparisons
are determined by their mate equations. The localization maps are the specified
counit and unit, and the finite boundary belongs to the evaluated same triangle.
No extra condition on the arbitrary base map or uniform levelwise Tor bound was
introduced. The sole theorem proof remains sorry as required for stage 2.

Validation: the prescribed scompile.py compiled the complete module cleanly in both
sandbox and library form. deliver2.py --no-push returned OK: preflight passed and
the per-file compile passed. No global build or direct git command was run.
