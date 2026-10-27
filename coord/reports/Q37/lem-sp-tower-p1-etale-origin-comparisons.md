## Worker report

Item: `lem-sp-tower-p1-etale-origin-comparisons`.
Module: `Sheaf.Paper.TowerP1EtaleOriginComparisons`.
Main declaration:
`AlgebraicGeometry.ProEtale.SpTowerP1.towerP1EtaleOriginComparisons`.

The theorem has one postponed proof, with the complete ten-step natural-language proof from
this node in its docstring. The other declarations are actual definitions or a proposition
structure. No definition contains `sorry`. The node statement and split are unchanged. Its statement dependencies gain only
the helper definition nodes listed below. There is no statement dispute.

### Hypotheses and objects

* Prime ell: `(l : ℕ) [Fact l.Prime]`.
* Finite extension: `(E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E]`. The recorded coefficient-extension integers are reused
  through `SpTowerShriek.R`, not replaced by a new valuation ring.
* Arbitrary base scheme with ell invertible: `(S : Scheme.{u})` and
  `(hS : IsUnit (l : Γ(S, ⊤)))`. There is no field, Noetherian, constructibility,
  finite-Tor, separatedness, or quasi-compactness assumption on the base.
* The positive coefficient level numbered n in the paper is indexed by `n - 1` in the
  existing tower interface: `SpTowerShriek.R l E k` is `O_E / (ell^(k+1))`.
  Its structural morphisms are the actual quotient transitions. This is the ell-power
  ideal, not a silent substitution of uniformizer powers when E is ramified.
* `Presentation l E S hS` supplies precisely the existing `TowerClasses` and normalized
  section-model operations in their fixed coordinates. It is the interface already used
  for the displayed geometric formulas, not an arbitrary choice of maps. Its
  `classes.base.realization` is sectionwise the recorded coefficient-tower category,
  and `SpTowerShriek.D` is its ordinary unbounded derived category.
* `SpTowerP1.domain l E b T` is `(∃ a : ℤ, DerivedCategory.IsGE K a)` together with
  `∀ n, Nonempty (SpTowerShriek.Origin l E b T n K)`. The latter retains an intrinsic
  level realization and the recorded `FixedEtaleOriginWitness` (bounded-below etale
  object plus a specified nu-star isomorphism). `C` is its full subcategory, retaining
  every ambient morphism. No compatible system of etale antecedents is assumed.
* `ProjectiveLine S`, `diagonalSurface S`, `ProjectiveLine S ↘ S`, `pullback.fst`,
  `pullback.snd`, and `diagonalImmersion S` give P, W, q, p1, p2, and Delta.
  `Etale.projectiveLineDiagonalProjection S false/true` names the two projections.
* `p.F` is the total right derived q direct image. `p.G` is exact q inverse image
  followed by tensor with the existing Tate line shifted by two. `p.delta` and
  `p.trace` are transports of the supported diagonal map and the inverse-splitting
  trace in `p.classes`; they are not new or freely supplied arrows. The other
  projective-line splitting traces are the same recorded construction over P.

### Conclusions, clause by clause

The main theorem asserts `∀ p : Presentation ..., ∃ d : Maps ..., EtaleOriginComparisons ...`.
Thus the normalizations are parameters and every closure/isomorphism/naturality assertion
is a conclusion, rather than an extra hypothesis imposed on K or M.

* Well-defined F and G: `Maps.push_closed` and `Maps.pull_closed`, with restrictions
  `left` and `rightRestricted` on the full categories `C`.
* Proper and qcqs q, p1, p2, Delta: fields `proper_q`, `qc_q`, `qs_q`,
  `proper_projections`, `qc_projections`, `qs_projections`, `proper_diagonal`,
  `qc_diagonal`, and `qs_diagonal`. The Bool quantifier includes both projections.
* Cartier diagonal and quasi-compact complementary open: `cartier_diagonal` is
  invertibility of the actual diagonal ideal; `qc_complement` is quasi-compactness
  of the open immersion for the complement of that ideal's support. This is a
  relative quasi-compact immersion, not absolute quasi-compactness of W or S.
* Exact Delta direct image: `diagonal_exact` asserts preservation of finite limits
  and finite colimits of the actual additive system direct image. The definition
  `diagonalExactComparison` constructs its canonical total-right-derived versus
  termwise-derived natural isomorphism using `rightDerivedFunctorIsoMapDerivedCategory`.
  It introduces no arbitrary isomorphism.
* The q projection: `Maps.projectionQ` is an isomorphism whose hom is fixed by
  `projectionQ_eq` to the counit-transpose `SpTowerP1.projection`. The library writes
  `Rq_*line[2] tensor K` and `line[2] tensor q^*K`; the retained signed symmetry
  identifies these with the order in the node and with `F(G K)`. The definition
  `epsilon` uses precisely these symmetries. `projection_q_bounded` bounds both
  endpoints of this canonical arrow.
* Supported projection for both p_i: `projection_diagonal` asserts invertibility
  of `projection Delta unit (p_i^*M)`. The existing `diagonalPull` and `leftUnit`
  identify its target with `RDelta_*M` by `p_i Delta = 1`. These are fixed
  composition and unit maps, not chosen target isomorphisms. The corresponding
  `projection_diagonal_bounded` bounds both endpoints, including the tensor
  source without assuming finite Tor amplitude.
* Both p_i line projections: `projection_projections` asserts invertibility of
  `projection p_i lineW[2] M`; symmetry gives the printed tensor order and twisted
  target. `projection_projections_bounded` supplies the two bounds.
* First proper exchange: `Maps.exchange` asserts invertibility of `p.exchange`.
  Its existing definition is the mate of the Cartesian-square pullback comparison
  using the unit of p2 and the counit of q. New `Presentation.exchangeSwap`
  constructs the identical mate with p1 and p2 exchanged, from the other unit and
  the same q counit; `exchange_swap` asserts its invertibility.
  `exchange_bounded` bounds all four endpoints.
* Composition source: `source_iso` asserts that the actual
  `p.sourceUnit M : M -> Rp2_*(RDelta_*M)` is invertible. This arrow is the
  composite of the p2 unit, the Delta unit, and `p.diagonalPull`, which uses the
  fixed ordinary compositor and identity normalization.
* eta and epsilon are the existing definitions `SpTowerP1.eta` and
  `SpTowerP1.epsilon`. Expanding eta gives sourceUnit, inverse supported projection,
  `p.delta tensor id`, symmetry, the inverse line-pullback comparison, inverse
  line projection, and inverse proper exchange, in that order. Expanding epsilon
  gives symmetry, inverse `projectionQ`, symmetry, `id tensor p.trace`, and the
  scalar-multiplication unitor. Thus the prescribed words are definitions rather
  than existential arrows satisfying only an abstract adjunction law.
* Their naturality is asserted by `eta_natural` and `epsilon_natural` for every
  morphism in the full domains. `etaTransformation` and `epsilonTransformation`
  package these components and these proofs as actual natural transformations.
  No triangle identity or adjunction theorem is added to this item.

### Equality of specified evaluated maps (repair F1 and F2)

The old `component_*`, `site_*`, and `root_comparison` conjuncts have been removed.
They repeated input geometry or generic site facts and did not state the item's
level equations. No claim that those old conjuncts were sufficient is retained.

`EtaleWords` now defines the ordinary etale pull, total direct image, tensor,
counit-transpose projection, both proper exchange mates, the diagonal pullback
identity and the pasted composition source. Its `delta` is the positive supported
Cartier Kummer class. Its `epsilon` is symmetry, inverse projection, symmetry,
identity tensor the splitting trace, and the scalar unitor. Its `eta` is the
pasted source unit, inverse supported projection, delta tensor identity, symmetry,
line pullback, inverse line projection and inverse exchange. Thus eta_n and
epsilon_n are actual formulas, not freely selected adjunction maps. The trace is
`ArbitraryBaseFiniteP1Splitting.trace`, the second projection of the inverse
unit/Chern splitting over the arbitrary scheme S.

`LevelWord` pairs an ordinary etale expression and its tower expression with a
comparison arrow. `originWord` uses exactly the supplied `Origin.witness.iso`
followed by `Origin.realization`. `pullWord` uses `exactSitePull`, the adjoint-
normalized coefficient realization and `Geometry.pullEvaluation`. `pushWord`
uses the specified site mate `exactSitePush`, the section-normalized realization
comparison on K-injective representatives and `Geometry.pushEvaluation`.
`tensorWord` uses the existing monoidal site comparison, realization fixed on
pure tensors and total K-flat representatives, and `Data.tensorEvaluation`.
`unitWord` sends constants to the same constants. `lineWord` sends a scalar times
an etale root to the same scalar times that root under `cartierRootsIso`, followed
by the recorded `lineEvaluation` and exact single/shift comparisons. These
normalizations rule out arbitrary endpoint isomorphisms.

`WordComparison K L f g` is the literal arrow equation

```
K.comparison ≫ SpTowerShriek.Ev.map f = nu.map g ≫ L.comparison
```

and asserts that both displayed endpoint comparisons are invertible. Hence the
following fields state the requested equalities after the specified identifications:

* `ProjectionLevelComparisons.q`, `.projections`, `.diagonal`: the three families
  of actual projections, including both p_i and every supplied origin of K or M.
* `ExchangeLevelComparisons.exchange`: both orders of the q/q proper exchange.
* `.diagonal_pull` and `.source`: composition for p_i Delta = identity, including
  both projection orders and the actual composition source map.
* `ClassLevelComparisons.delta`, `.trace`, `.shifted_line`: the supported class,
  splitting trace, and shifted line comparison used inside the words.
* `FormulaLevelComparisons.eta` and `.epsilon`: the decisive equations for the
  defined tower eta/epsilon and nu-star of the explicit finite formulas. They
  quantify over EVERY `Origin` witness; there is no compatibility requirement
  among witnesses at different levels and no chosen replacement witness.

The main `levels` field supplies these conclusions at each positive level, for
normalized projective coordinates, using the actual finite quotient. In
particular `.eta` exposes precisely e_n eta = nu-star eta_n under its canonical
endpoint maps, as needed by `lem-sp-tower-p1-single-level-triangles`.

### Dependency declarations used

* `def-weil-l-adic-coefficient-extension`:
  `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`,
  `Padic.finite_coefficientExtensionRing` and the reexported
  `Padic.coefficientExtensionIntegers`; the ell-power quotient is the recorded
  `SpTowerShriek.R`, with finite instance from `Base.finite`.
* `sk-def-sp-coefficient-towers`:
  `Sheaf.Paper.SmoothPurityCoefficientTowers`, `spCoefficientTowers`, `spEllIdeal`,
  and `spCoefficientReduction` (namespace `AlgebraicGeometry.ProEtale`).
* `det-sp-coefficient-towers-abelian`:
  `Sheaf.Paper.SmoothPurityCoefficientTowersAbelian`,
  `AlgebraicGeometry.ProEtale.SpCoefficientTowersAbelian` and
  `sp_coefficient_towers_abelian`. `Base.realization` retains these coordinates.
* `def-weil-pbc-etale-origin-witness`:
  `Sheaf.AlgebraicGeometry.FixedEtaleOriginWitness`,
  `AlgebraicGeometry.Scheme.FixedEtaleOriginWitness`, through `SpTowerShriek.Origin`.
* `def-nagata-projective-space-base-change`:
  `WeilConjectures.AlgebraicGeometry.ProjectiveSpace`,
  `AlgebraicGeometry.ProjectiveSpace`, through its existing `ProjectiveLine` alias.
* `det-sp-tower-classes`: `Sheaf.Paper.SmoothPurityTowerClasses`,
  `AlgebraicGeometry.ProEtale.TowerClasses`, its Chern and supported boundary
  normalizations and its actual inverse-splitting trace.
* `lem-coef-semilinear-derived-sections`: `Sheaf.Paper.SemilinearDerivedSections`,
  `WeilConjectures.SemilinearSections.SemilinearDerivedSectionsData`,
  `semilinearDerivedSections`, and `Geometry.ProjectionEvaluation`. The existing
  `SpTowerShriek.Base`, `Geometry`, and `Operations` specialize this normalized
  calculus to the recorded towers.
* `lem-weil-pbc-comparison-direct-image-canonical-mate`:
  `Sheaf.AlgebraicGeometry.FixedComparisonDirectImageMate`,
  `AlgebraicGeometry.ProEtale.fixedComparisonDirectImageMatePlus` and
  `fixedComparisonPullbackPlus`. The predicate copies the recorded counit equation.

All eight dependency nodes and the source signatures/docstrings were read. Additional
existing helper definitions are reused from `Sheaf.Paper.SmoothPurityTowerP1Adjunction`:
`SpTowerP1.domain`, `C`, `TensorData`, `Presentation`, `projection`, `Maps`, `left`,
`rightRestricted`, `eta`, and `epsilon`. Its theorem `exists_towerP1Adjunction` is
neither invoked nor used in defining any object of this delivery. That downstream
node is not added to stmt_deps: only its already published helper definitions are
reused, to obey one definition per notion. When stage 3 proves that downstream
theorem using this result, the shared definitions should be imported from a common
interface rather than adding a reverse import to this module. No import cycle is
introduced by this delivery.

### Edge cases

Checked the empty base and empty diagonal, zero coefficient objects, the first positive
level, ramified coefficient extensions, arbitrary non-quasi-compact base, and unbounded
Tor amplitude of bounded-below inputs. The complementary-open claim is relative and
local on the target; no absolute compactness of S is introduced. The full domain does
not restrict morphisms or demand transition-compatible origin witnesses. All functors
live in the ordinary unbounded system localization before the full D+ restriction.
The fixed scalar coefficient universe is u+1 on the small sites (objects u+1,
morphisms u); no equality of those distinct site universes is imposed. The ordinary
constant-ring/fixed-module transports are the published intrinsic equivalences.

### Searches

Before writing, the prescribed msearch wrapper was used with:

* LeanFinder: `Projective line coefficient towers etale origin canonical projection
  formula proper exchange unit counit comparison` — eight unrelated ordinary
  etale algebra/presentation hits; no matching tower result.
* Loogle: `CategoryTheory.Adjunction, CategoryTheory.IsIso` — twelve general
  adjunction/isomorphism hits; none states this result.
* Mathlib grep: `TowerP1|tower.*etale.*origin|etale.*origin.*tower` — no hits.
* LeanSearch: `Projective line coefficient towers etale origin proper projection
  exchange canonical comparison` — eight unrelated projective/etale results;
  none states the coefficient-tower comparison.
* `rg` in `lean/WeilConjectures` and `lean/Sheaf` for the item id, tower P1,
  etale-origin, proper projection, comparison, and existing eta/epsilon formulas;
  literal `grep -rn` for the item id in `lean/WeilConjectures` — no declaration
  for this node. The parent helper module was found and reused. Further targeted
  searches located the actual projection-mate square, both site exchange
  comparisons, root comparison, exact functor localization comparison, and
  component projection evaluation, instead of defining private copies.

Source read: `literature/blueprint/latest/blueprint/sec-smooth-purity/`
`sk-prop-sp-tower-geometric/sk-prop-sp-tower-geometric-p1.proof.md`, especially
Reduction, Levelwise check, and Levels; the DAG's complete ten-step split supplies
the detailed construction and compatibility argument in the theorem docstring.

### Validation

Every delivered file is checked through scompile.py, separately in dependency order,
against the live published library. The final compiler and delivery results are recorded
below after the last run. Every variable and universe is explicit; autoImplicit is false.
Diagnostic probes are removed from the packet.

## Second reading by Q37

This is a separate self-review of the node, source and all helper definitions. No other
agent was started, in accordance with the dispatcher's explicit prohibition. The
maintainer supplies the independent reading.

The review checked both projections and swapped exchange, all boundedness clauses,
every retained origin, the signed tensor symmetries, finite eta/epsilon definitions,
and the actual comparison-square equations. The repaired level assertion contains
no componentProjection, siteProjectionSquare, siteMateSquare or root_comparison
stand-in. Constant and root coordinate maps are normalized sectionwise; tensors are
normalized on pure sections, signed total inclusions and K-flat representatives;
pushforward is normalized on every K-injective representative; pullback is its mate.
Only the main theorem has a postponed proof. The finite formulas and all coordinate
predicates have real definitions and each helper module has an owning DAG node.

## Returned-delivery repair

H3: this is a substantive rewrite of the returned main module (returned hash prefix
`eec77f8e`), not an unchanged re-push. The main file removes the hollow fields,
imports the finite formula comparison module, and adds `levelComparisons` and
the `levels` conclusion. The report and node lean/dependency records are updated.

F1: added the ordinary etale words, actual finite eta_n/epsilon_n definitions,
and direct commuting-square equations for the evaluated maps, universally in the
retained Origin witness. F2: removed the hollow component/site/root conjuncts;
replaced them with the projection, exchange, composition, class, and complete
formula equations above. The valid geometry, isomorphism, boundedness,
naturality, and `forall p, exists d : Maps` clauses are retained.

The advisory about the parent module is recorded: this delivery uses its
published helper definitions but never its adjunction theorem. Before stage 3,
the maintainer should split those helpers out of SmoothPurityTowerP1Adjunction
into their owning definition module to avoid a proof import cycle.

No statement correction or dependency-node repair is needed. New definition nodes own the finite words and normalized coordinate interfaces needed to state the level clauses; all are cited from the item. No extra theorem is postulated.


## New nodes

`def-sp-p1-tensor-ordinary-coordinates` (Sheaf.Paper.TowerP1TensorOrdinaryCoordinates): Define the fixed-module pro-etale sheaf category and its canonical associated-module-sheaf realization at a positive coefficient level. TensorOrdinaryCoordinates consists of ordinary tensor isomorphisms whose maps send every pure tensor of scalar-unit sections to the tensor of those same sections. Source: current blueprint Construction/Levels. The three grouped msearch searches and repository/blueprint search recorded in its mathlib_searches found generic ingredients but no exact interface; those ingredients are imported and reused.

`def-sp-p1-fixed-total-tensor` (Sheaf.Paper.TowerP1FixedTotalTensor): Define fixedTotalTensor as the uncurry of the existing direct-sum total cochain tensor of fixed-module pro-etale sheaves, with its existing signed differential. Source: current blueprint Construction/Levels. The three grouped msearch searches and repository/blueprint search recorded in its mathlib_searches found generic ingredients but no exact interface; those ingredients are imported and reused.

`def-sp-p1-tensor-chain-coordinates` (Sheaf.Paper.TowerP1TensorChainCoordinates): Define the intrinsic signed total tensor and its inclusions. TensorChainCoordinates extends the ordinary pure-tensor coordinates by the termwise realization map on total complexes, required to commute with every summand inclusion indexed by integers i+j=k. Source: current blueprint Construction/Levels. The three grouped msearch searches and repository/blueprint search recorded in its mathlib_searches found generic ingredients but no exact interface; those ingredients are imported and reused.

`def-sp-p1-tensor-derived-coordinates` (Sheaf.Paper.TowerP1TensorCoordinates): Define TensorCoordinates to extend the signed chain coordinates by a derived tensor natural isomorphism, preservation of K-flat complexes, and the commuting equation on every pair of K-flat representatives through the existing localization factors and section-model tensor comparison. Source: current blueprint Construction/Levels. The three grouped msearch searches and repository/blueprint search recorded in its mathlib_searches found generic ingredients but no exact interface; those ingredients are imported and reused.

`def-sp-p1-etale-operations` (Sheaf.Paper.TowerP1EtaleOperations): For a commutative ring A and schemes, use ordinary etale derived pullback, direct image and tensor. Define the projection as the transpose of the counit. For P=P^1_S, W=P times_S P and its diagonal Delta, define diagonalPull through the canonical pullback compositor and identity, sourceUnit through the pasted adjunction units, diagonalProjection through projection and the scalar unitor, and exchange for both orders of the two projections through the Cartesian square mate. Source: current blueprint Construction/Levels. The three grouped msearch searches and repository/blueprint search recorded in its mathlib_searches found generic ingredients but no exact interface; those ingredients are imported and reused.

`def-sp-p1-etale-diagonal-word` (Sheaf.Paper.TowerP1EtaleDelta): For a finite commutative ring A killed by a positive integer N invertible on W=P^1_S times_S P^1_S, define the shifted line to be A(1)[2] and delta: RDelta_* A_P to A_W(1)[2] to be the positive supported Cartier Kummer boundary, converted to the ordinary etale derived category by the specified Cartier reduction. Source: current blueprint Construction/Levels. The three grouped msearch searches and repository/blueprint search recorded in its mathlib_searches found generic ingredients but no exact interface; those ingredients are imported and reused.

`def-sp-p1-etale-word-invertibility` (Sheaf.Paper.TowerP1EtaleFiniteData): For a finite commutative ring A killed by N and a scheme S, define InvertibleWords as invertibility, on all derived inputs, of the named q projection with the shifted line, the p2 projection with p1 pullback and shifted line, diagonalProjection for p1, and the proper q/q exchange. This predicate supplies the inverse arrows in the finite formulas. Source: current blueprint Construction/Levels. The three grouped msearch searches and repository/blueprint search recorded in its mathlib_searches found generic ingredients but no exact interface; those ingredients are imported and reused.

`def-sp-p1-etale-epsilon-word` (Sheaf.Paper.TowerP1EtaleEpsilon): For finite A killed by N invertible on S, use the positive unit/Chern projective-line splitting and its trace. Define epsilon_K by the inverse canonical q projection on the shifted line, tensor symmetry, tensor with the splitting trace, and the scalar unitor, from Rq_*(q^*K tensor A(1)[2]) to K. Source: current blueprint Construction/Levels. The three grouped msearch searches and repository/blueprint search recorded in its mathlib_searches found generic ingredients but no exact interface; those ingredients are imported and reused.

`def-sp-p1-etale-eta-word` (Sheaf.Paper.TowerP1EtaleWords): For finite A killed by positive N invertible on the projective-line product and the Cartier diagonal, define eta_M by sourceUnit for p2, inverse diagonalProjection for p1, delta tensor identity, symmetry, the specified shifted-line pullback, inverse projection for p2, and inverse proper exchange. Its target is q^*Rq_*M tensor A(1)[2]. Source: current blueprint Construction/Levels. The three grouped msearch searches and repository/blueprint search recorded in its mathlib_searches found generic ingredients but no exact interface; those ingredients are imported and reused.

`def-sp-p1-ordinary-push-coordinates` (Sheaf.Paper.TowerP1OrdinaryPushCoordinates): At a finite coefficient level, define OrdinaryPushCoordinates for f:X to Y as the natural isomorphism from realization followed by actual constant-ring direct image to fixed-module direct image followed by realization, sending every scalar-unit section to the same section. Define its termwise complex map and the canonical realized K-injective source model. Source: current blueprint Construction/Levels. The three grouped msearch searches and repository/blueprint search recorded in its mathlib_searches found generic ingredients but no exact interface; those ingredients are imported and reused.

`def-sp-p1-derived-push-coordinates` (Sheaf.Paper.TowerP1PushCoordinates): Define PushCoordinates to extend the scalar-section normalized ordinary direct-image coordinates with a derived natural isomorphism. On every K-injective fixed-module representative it must equal the termwise ordinary comparison under the canonical right-derived model isomorphisms and exact realization localization factors. Source: current blueprint Construction/Levels. The three grouped msearch searches and repository/blueprint search recorded in its mathlib_searches found generic ingredients but no exact interface; those ingredients are imported and reused.

`def-sp-p1-geometric-coordinates` (Sheaf.Paper.TowerP1GeometricCoordinates): Define GeometricCoordinates to extend normalized direct-image coordinates by a derived pullback isomorphism whose adjoint mate is exactly the inverse direct-image comparison. Define exactSitePull from the published exact/left-derived pullback and site-comparison isomorphisms, and exactSitePush as its ordinary total-derived adjoint mate. Source: current blueprint Construction/Levels. The three grouped msearch searches and repository/blueprint search recorded in its mathlib_searches found generic ingredients but no exact interface; those ingredients are imported and reused.

`def-sp-p1-level-words` (Sheaf.Paper.TowerP1LevelWords): Define a LevelWord on T by a tower object, ordinary etale object, and comparison from nu-star of the latter to evaluation of the former. Define originWord from the retained witness and realization; pullWord, pushWord and tensorWord recursively through the specified site, coefficient-realization, and evaluation comparisons. WordComparison(K,L,f,g) requires the two comparison arrows to be invertible and the equation c_K composed with Ev_n(f)=nu-star(g) composed with c_L. Source: current blueprint Construction/Levels. The three grouped msearch searches and repository/blueprint search recorded in its mathlib_searches found generic ingredients but no exact interface; those ingredients are imported and reused.

`def-sp-p1-coefficient-coordinates` (Sheaf.Paper.TowerP1CoefficientCoordinates): Define CoefficientCoordinates at a positive level with invertible exponent on T as the ordinary constant and Tate-line comparison isomorphisms, normalized on every constant scalar section and every scalar times root section through the published Cartier root-site isomorphism. Define the constant and shifted-line LevelWords using exact single-complex and shift comparisons and the specified tower lineEvaluation. Source: current blueprint Construction/Levels. The three grouped msearch searches and repository/blueprint search recorded in its mathlib_searches found generic ingredients but no exact interface; those ingredients are imported and reused.

`def-sp-p1-projective-coordinates` (Sheaf.Paper.TowerP1ProjectiveCoordinates): For a normalized projective-line tower presentation over S with l invertible, define ProjectiveCoordinates at a finite level to consist of the preceding normalized geometric and tensor coordinates, constant and line coordinates on S, P and W, the specified finite twist transport, positive unit/Chern splitting and named finite invertibility data. Define its recursive push, pull, tensor, constant and line words; define both diagonal identities, composition source units and swapped exchange using the given tower adjunctions. Source: current blueprint Construction/Levels. The three grouped msearch searches and repository/blueprint search recorded in its mathlib_searches found generic ingredients but no exact interface; those ingredients are imported and reused.

`def-sp-p1-projection-level-comparisons` (Sheaf.Paper.TowerP1ProjectionLevelComparisons): For the normalized projective-line coordinates, define ProjectionLevelComparisons to require WordComparison for q with the shifted line, both projections with the shifted product line, and Delta with the constant object and both pulled inputs. Define ExchangeLevelComparisons for both ordered proper exchanges, both diagonal pullback composition identities and both composition source units. Every input in the full bounded-below etale-origin domain is quantified together with every retained Origin witness. Source: current blueprint Construction/Levels. The three grouped msearch searches and repository/blueprint search recorded in its mathlib_searches found generic ingredients but no exact interface; those ingredients are imported and reused.

`def-sp-p1-formula-level-comparisons` (Sheaf.Paper.TowerP1FormulaLevelComparisons): For normalized projective-line coordinates and Maps d, define ClassLevelComparisons by WordComparison for the actual tower delta, splitting trace and shifted-line pullback against their finite etale words. Define FormulaLevelComparisons by WordComparison for the complete tower eta_M and epsilon_K against the explicit finite diagonal eta_n and splitting-trace epsilon_n formulas, for every bounded-below etale-origin object and every supplied Origin witness. Endpoints use the recursively specified word comparisons, not arbitrary endpoint isomorphisms. Source: current blueprint Construction/Levels. The three grouped msearch searches and repository/blueprint search recorded in its mathlib_searches found generic ingredients but no exact interface; those ingredients are imported and reused.


The ordinary push coordinate interface is for the actual
`proEtaleConstantRingPushforward` used in `Geometry.pushEvaluation`, with the
constant-section adjoint scalar action. The published
`sfIntrinsicDirectImageComparison` targets `proEtaleConstantModuleDirectImage`,
the rho-based sectionwise pushforward. Its normalization is reused as the
specification here, for the c-based ringed adjunction; it is not substituted for
the geometric operation. The representative equation fixes the derived comparison
on all K-injective complexes, and its adjoint mate fixes pullback.

## Final validation

All eighteen delivered files compiled cleanly through scompile.py in both sandbox
and library coordinates, with no errors or warnings. The main theorem compiled
in 5.4 seconds in library coordinates. The only postponed proof is the main
theorem. The first full preflight requested the current schema's import_flags
field on the seventeen new nodes; empty lists were added. No mathematical
statement was changed to resolve a compiler or preflight diagnostic.
