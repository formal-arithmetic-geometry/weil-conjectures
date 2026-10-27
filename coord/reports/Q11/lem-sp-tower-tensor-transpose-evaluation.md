## Worker report

The delivery states `AlgebraicGeometry.ProEtale.SpTensorTranspose.tensor_transpose_evaluation`
in `Sheaf.Paper.TowerTensorTransposeEvaluation`. Its only new theorem has proof `sorry`.
All helper definitions contain actual data. The item's statement, dependencies and proof
are unchanged; only its `lean` record is added. There are no new DAG nodes, dependency
statement repairs or mathematical statement corrections.

The source read is the CURRENT
`literature/blueprint/latest/blueprint/sec-smooth-purity/sk-prop-sp-tower-geometric/sk-prop-sp-tower-geometric-gamma.proof.md`,
paragraph (2), together with all five proof steps of this node. The current source agrees
with the node: construct the transpose on towers, evaluate it, then compose the orientation.

### Hypotheses and objects

* The finite field, its characteristic and algebraic closure are `D : FiniteFieldDatum`.
  `l : ℕ`, `[Fact l.Prime]`, `_hne : l ≠ D.p` give the distinct coefficient prime.
  `E : Type u`, `[Field E]`, `[Algebra (Padic l) E]` and
  `[FiniteDimensional (Padic l) E]` give exactly an arbitrary finite coefficient extension.
  The ring of integers and specified uniformizer are Padic's published constructions.
* `b : SpTowerShriek.Base l E` retains the equation `l = u * pi ^ e`, positivity of e,
  equality of coefficient ideals, and the finite quotient coefficients. Its `R l E n`
  is literally O_E/(ell)^(n+1). `b.ideals n` identifies this with uniformizer exponent
  `b.ramification * (n+1)`, rather than confusing ell and uniformizer exponents.
  The natural index `n` is a predecessor: n=0 is the required FIRST positive level.
* `X` and `Y` are schemes over `Spec D.k` with separated, locally finite-type and
  quasi-compact structure morphisms. `(j ≫ p).IsOver` gives a morphism over that field;
  `[SmoothOfRelativeDimension d (j ≫ p)]` and `d : ℕ` give smoothness and pure dimension.
  Here the node's f is written using a chosen compactification `j : X ⟶ Z`,
  `[IsOpenImmersion j]`, `p : Z ⟶ Y`, `[IsProper p]`. There is no restriction on which
  compactification is chosen. Every separated finite-type f has one by Nagata.
* The explicit `[IsNoetherian X]`, `[IsNoetherian Y]`, `[QuasiCompact (j ≫ p)]` and
  `[HasCompactification (j ≫ p)]` are the already recorded finite interfaces' proposition
  witnesses; they follow from finite type over the field and the displayed factorization,
  so impose no extra mathematical case restriction. `[Finite (R l E n)]` is `b.finite n`.
* `o : SpTowerShriek.Operations`, `q : SpTowerCalculus.Coordinates` and
  `SpTowerCalculus.C l E b q T` use the existing ordinary derived category and its FULL
  uniformly constructible finite-Tor subcategory. They are not diagrams of derived objects,
  and there is NO `IsSpNormalizedTower` assumption on K or Q.
* `hF`, `G`, `adj` and `lv : SpTowerGluing.Levels ...` give exactly the existing tower
  compact-support restriction, exceptional adjoint, adjunction, finite right-adjoint
  comparisons and their unit/counit compatibilities. No new adjunction is assumed on
  an unrestricted pro-etale ambient category.
* `SpTowerGamma.unit` is the coefficient tower in degree zero. `originalUnit` changes
  only to the original strict-tower coordinates; `hU` is its membership in C_Y.
  `SpTowerGamma.exceptional ... G` realizes G in section-preserving system coordinates.
  Its value at this unit is omega. `lv` identifies its finite evaluations with omega_n.
* `tx` and `ty : SpTowerP1.TensorData ...` are the existing normalized signed K-flat
  symmetry and scalar unit identifications. They are not arbitrary braidings or unit maps:
  `closed_eq`, `unit_normalization`, and the RingedSiteDualityModel fix them.
* `w : SpChartAdmissibility.Twists`, `roots : SpCoordinateAdjunction.RootLines`,
  `hX`, `hY`, `ccX`, `ccY`, `tc : TensorCoordinates`, `gc : GeometricCoordinates` are
  the PUBLISHED coefficient, root, K-flat tensor and site-pullback comparison coordinates.
  Section identities, representative equations and the adjoint mate equation normalize
  them. Invertibility of ell on X and Y follows from ell differing from the characteristic.
* `a` is the arbitrary given tower orientation. Its source `orderedLine ... w d` is the
  existing ordered tensor presentation of 1_X(d)[2d]. `alpha` is its specified finite
  diagonal orientation: `_halpha : OrientationNormalized ... alpha` fixes its actual
  Rees/deformation/Kummer normalization, rather than choosing any endpoint isomorphism.
  `_ha : WordComparison ... a.hom ... alpha.inv ...` is exactly a_n = Pi_n^(-1).
* `ui` identifies the retained ordinary-etale origin of the unit with the actual finite
  coefficient unit. `_hui` fixes its scalar normalization by the published `unitWord`;
  thus this identification cannot hide a scalar factor.
* `hQ : ∀ K, spConstructibleTorTowers ... (inverse.obj (tensorSource.obj K))` is precisely
  the explicit assumption Q_K ∈ C_X, for EVERY K ∈ C_Y. It does not assume flatness of K.
  `hpf : ∀ K, IsIso (SpTowerShriek.projection ... omega K)` is the other explicit
  hypothesis: invertibility of the SPECIFIED compactification projection transformation.

The theorem is parametrized by an arbitrary n and its normalized finite comparison data;
applying it for each n gives every positive level of the node's conclusion. Naturality is
asserted on ALL tower arrows K -> L and is not inferred from its finite evaluations.

### Every conclusion and displayed formula

1. `SpTowerGamma.projectionCounit` is h_K. Its data is, verbatim, F(symmetry), inverse of
   `SpTowerShriek.projection`, target symmetry, `1 tensor counit`, and `ty.rightUnit`.
   `SpTowerShriek.projection` itself uses the prescribed proper adjunction transpose,
   open tensor comparison and pullback composition; it is not a freely supplied iso.
   The FIRST conjunct says F(q_v) ≫ h_L = h_K ≫ v in the ordinary tower derived category.
2. `SpTowerGamma.tensorMate` is t_K. Its `adj.homEquiv` is literally the formula
   `eta_Q ≫ G.map h_K`, with the full inclusion and fixed realization equivalence
   supplying unique Hom preimages. `originalSource` and `originalComposite` expose Q
   and h in the original full category using those same expressions. The SECOND
   conjunct says q_v ≫ t_L = t_K ≫ G(v) in the ambient ordinary tower category.
3. The THIRD conjunct is naturality of the actual `SpTowerGamma.gamma` arrow.
   Its definition is tensor(identity, a.hom) followed by the actual tensorMate.
   `source`/`orderedLine` are the existing ordered shifted tensor presentation;
   the canonical even-shift reassociation tau is already absorbed into that presentation.
   Thus this is g = t (1 tensor a) tau, including d=0.
4. The final universally quantified K clause first supplies invertibility of the
   canonical source comparison `tensorWord.comparison`. `dualizingWord` uses exactly
   the finite comparison of G, the unit normalization and the UNIQUE right-adjoint
   comparison `finiteRightComparison`; `tensorWord` then uses the published `pullWord`
   and `tensorWord` comparisons, fixed on K-flat representatives.
5. The first finite equation evaluates `originalComposite` by exact derived evaluation
   and `lv.support_evaluation`. Its right side is the finite inverse hom equivalence
   applied to `intrinsicTheta`. `finiteTheta` is the EXISTING specified finite
   `Etale.smoothTensorDualityMap` followed by the unique right-adjoint comparison.
   That map is DEFINED as the adjoint transpose of symmetry, inverse projection,
   symmetry, identity tensor counit and right unitor. Consequently its inverse
   hom equivalence is exactly h_(f,R_n,K_n), the requested finite h formula.
   `intrinsicTheta` only conjugates that map through the fixed source, target,
   realization and finite-adjoint comparisons; it supplies no independent map data.
6. The next `WordComparison ... tensorMate ... finiteTheta` says exactly (t_K)_n = theta.
   `WordComparison` includes invertibility of both endpoint comparisons and the explicit
   commuting square `sourceComparison ≫ Ev.map t = nu.map theta ≫ targetComparison`.
7. The last `WordComparison ... gamma ... Etale.FiniteSmoothPurity.gamma ...` says
   exactly (g_K)_n = gamma_(f,R_n)(K_n), with the coefficient, tensor, pullback,
   adjunction and twist-reassociation comparisons explicit. Finite gamma is its
   published three-factor tensor definition, using the normalized diagonal alpha.
8. Every arrow above was constructed BEFORE evaluation. No hypothesis about lifting
   arbitrary finite derived arrows, faithfulness of evaluation, or normalized input
   towers occurs anywhere in the signature or helper definitions.

The finite equality is expressed in the ordinary-etale origin coordinates retained by
`SpTowerGluing.Levels.realization`; the normalized comparison `nu` carries its maps to
exactly the original small-pro-etale intrinsic categories. This is the same canonical
comparison presentation already used by the parent tower-gamma declaration, not a
replacement coefficient theory or a special family of finite input objects.

### Declarations of dependencies read and used

* `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum` and its field instances.
* `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing`; the recorded integer ring/uniformizer quotients.
* `def-weil-scheme-morphism-properties` is a collection node, with no individual Lean
  declaration. Its individual properties are the existing Mathlib scheme properties.
* `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `Smooth`, `SmoothOfRelativeDimension`.
* `Sheaf.Paper.SmoothPurityCoefficientTowers`: `spCoefficientTowers`, `spEllIdeal`.
* `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`, `HasDerivedCategory`.
* `Sheaf.Paper.SmoothPurityCoefficientTowersAbelian`: `SpCoefficientTowersAbelian`,
  `spCoefficientEvaluation`, the exact ordinary-derived level evaluation interface.
* `Sheaf.Paper.SmoothPurityNormalizedTowers`: `spConstructibleTorTowers`,
  `spConstructibleTorTowerCategory`, `spDerivedCoefficientEvaluation`. The node's recorded
  main declaration names the normalized subcategory, but this SAME module also supplies
  the unnormalized category that its first paragraph explicitly defines; that is used.
* `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor`: `derivedTensor`.
  The ordinary ring-system tensor is the recorded `SpTowerShriek.tensor`, not an integral
  completed tensor. Its finite normalized coordinates compare it with this derived tensor.
* `Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted` publicly retains the existing
  finite, integral and common-stage coefficient-twist definitions. The actual tower
  positive line uses the same recorded `SpCoordinateAdjunction.line` and finite root line.
* `Sheaf.Paper.SmoothPurityTowerGluing`: `support`, `level`, `Levels` (including
  `comparison`, `unit`, `counit`, `realization`, `support_evaluation`), `tower_gluing`.
* `Sheaf.Paper.DerivedPullbackTensorHom`: `finiteDerivedPullback`,
  `finiteIntrinsicDerivedTensor`; in the tower coordinates these are the fixed
  `SpTowerShriek.pull` and normalized finite pullback comparison.
* `Sheaf.Paper.PurityDiagonalDualizingObject`: the canonical normalized diagonal
  orientation; imported for the proof dependency, while the theorem takes the orientation
  as hypothesis using `FiniteSmoothPurity.OrientationNormalized` in its retained finite
  Rees/deformation coordinates.
* `Sheaf.Paper.SmoothPurityTowerShriekLevels`: `Base`, `Operations`, `D`, `Ev`,
  `tensor`, `projection`, `Fcomparison`; `CoefficientTowerShriekInterfaces` supplies the
  normalized `Coordinates`, `C`, `realization`, `levelComparison` and evaluation records.
* `Sheaf.Paper.ExchangeProjectionSuppliedDomains`: the specified compactification
  projection word (`compactificationProjectionFromData`, `ExchangeProjectionStage.projection`).
  The recorded tower `projection` uses that same proper counit-transpose/open word.
* `Sheaf.Paper.CohomologicalSmoothnessFiniteComparison`: its recorded tensor clause
  uses the ordinary `Etale.dualizingComplexTensorMap`; the reordered canonical transpose
  used here is the published `Etale.smoothTensorDualityMap`, with the SAME counit word.
* `Sheaf.Paper.SmoothPurityMap`: `smoothPurityUnitIso`, `smoothPurityEtaleTheta`,
  `smoothPurityTheta`, `smoothPurityMap`; the finite equation uses the already published
  `Etale.FiniteSmoothPurity.gamma` presentation from `FiniteSmoothPurityMaps`.
* `Mathlib.CategoryTheory.Adjunction.Basic`: `Adjunction.homEquiv`, its explicit unit
  formula and naturality, read to verify the actual transpose formulas.

### Edge cases

* d=0: orderedLine is the coefficient unit; both finite and tower gamma retain the
  actual unit comparisons and the zero shift. No positivity hypothesis on d is added.
* n=0: R is O_E/ell, corresponding to uniformizer exponent e, not O_E and not zero.
  The first positive level is covered. Every other positive level is n+1.
* Ramified e>1: `b.ideals n` transports the actual quotient; no unramified assumption
  or equality of ell and the uniformizer appears.
* K=0, zero arrows, arbitrary tower transitions and NON-normalized towers are allowed.
  Every naturality equation is an equation between actual derived arrows, including zero.
* Empty X or Y: the scheme, finite-type and smooth interfaces allow emptiness; coefficient
  scalar maps and unit normalization remain defined, and no nonempty scheme binder appears.
* Sites retain object universe u+1 and morphism universe u with coefficients lifted to
  u+1; these have not been equated. There is no extraneous indexing universe restriction.

### Searches

The prescribed msearch tools were run under Q11 and this item:

* `leanfinder`: "Evaluation of the adjoint transpose of the tower projection formula
  counit equals the finite smooth purity map". Eight hits, all smooth-manifold sheaf
  evaluation maps (`smoothSheaf.ι_evalHom` and variants); none is a tower theorem.
* `loogle`: `CategoryTheory.Adjunction.homEquiv`. Twelve abstract hom-equivalence hits,
  including `homEquiv_apply` and `homEquiv_naturality_right`; no geometric tower assertion.
* `grep`: `projection.*counit|counit.*projection`, Mathlib CategoryTheory. Zero hits.
* `leansearch`: "Evaluation of adjunction transpose natural transformation derived
  coefficient towers". Eight hits on generic derived units/counits, evaluation
  adjunctions and constant presheaves; no matching coefficient-tower assertion.
* `rg` of `lean/WeilConjectures`, `lean/Sheaf` and `dag/lean_names_upstream.json` for the
  item ID, tower tensor transpose names and proposed namespace found no matching theorem.
  `SmoothPurityTowerGamma` contains the needed DEFINITIONS and a downstream proof-plan
  mention of this item, which is why those definitions are reused, never duplicated.
* Read the existing `WordComparison`, `LevelWord`, `TensorCoordinates`,
  `GeometricCoordinates`, `CoefficientCoordinates`, finite canonical gamma and theta
  definitions in full. These already give every needed notion; no new definition node
  is required. The six small helpers introduced here only expose the existing composites
  and their coordinate conjugations, and are listed in `lean.declarations`.

No STATEMENT-DISPUTED or mathematical node fault was found.

### Returned-delivery repair: declaration ownership

The return on immutable head b34c19561ba2 identified 18 duplicate declarations. The
current live `Sheaf.Paper.SmoothPurityTowerGamma` still owns all of them. This repair
removes their entire local declaration block and imports that existing module instead.
The reused `AlgebraicGeometry.ProEtale.SpTowerGamma` declarations are:
`coefficientWord`, `counit`, `exceptional`, `factorization`, `finiteRightComparison`,
`gamma`, `inputWord`, `lineWord`, `orderedLine`, `originalUnit`, `projectionCounit`,
`realization`, `rootWord`, `source`, `targetWord`, `tensorMate`, `tensorSource`, and `unit`.
None is renamed or redeclared. The sandbox's former replacement consumer module is
removed from this delivery, so the live owning module needs no modification.

The item's six local helper definitions and theorem signature are unchanged from the
returned head. The node's `lean.declarations` now lists only declarations this module
actually owns. Its `lean.note` records the import and reuse. No mathematical statement,
DAG dependency or proof plan changes. The imported `tower_gamma` theorem is not used in
the statement or any helper data: the import supplies the existing actual maps and
coordinate constructions requested by the return.

Validation uses only the prescribed scompile.py and deliver2.py wrappers. The repaired
module passed server compilation against the live published build (31.4 s sandbox,
28.5 s library) with no errors or warnings. Dry-run and delivery use the same packet.

## Second reading by Q11

This is the maintainer's second reading. The worker's section here only said that no second
reading had been done. I read the node, its source place (tower-geometric gamma proof (2)),
every statement dependency, the item module, the live owning module
Sheaf.Paper.SmoothPurityTowerGamma, and the earlier returned head b34c19561ba2.

What changed since b34c: the 18 SpTowerGamma definitions are no longer copied. The module
imports `Sheaf.Paper.SmoothPurityTowerGamma`, where det-sp-tower-gamma owns all 18 names,
and `lean.declarations` lists only the six local helpers and the theorem. The helper bodies
and the theorem signature are byte-identical to b34c, and `lean.statement` matches the file
verbatim. Apart from `lean`, the item node is identical to live.

Node clauses and their Lean renderings:

* k_0, k, p, ell != p and finite E/Q_ell are `D : FiniteFieldDatum`, `_hne`, `[Fact l.Prime]`
  and `E` with `[FiniteDimensional (Padic l) E]`. `b : SpTowerShriek.Base` keeps
  `ell = u varpi^e`, and `R l E n = O_E/ell^(n+1)`, so n = 0 is the first positive level. OK.
* X and Y are separated finite-type k-schemes. f is `j ≫ p`, with
  `[SmoothOfRelativeDimension d (j ≫ p)]`. The compactification (j, p) is arbitrary: it is
  the specified compactification of def-exchange-projection. The IsNoetherian, QuasiCompact
  and HasCompactification instances follow from the node's hypotheses. OK.
* C_T is `SpTowerCalculus.C`, the full uniform ctf subcategory, with no normalization. F, G
  and the finite comparisons are `hF`, `G`, `adj` and `lv` from det-sp-tower-gluing. OK.
* omega is `exceptional.obj ⟨originalUnit, hU⟩`. a is an arbitrary iso from
  `orderedLine X w d`. Its level n is the finite diagonal orientation through `_halpha`
  (OrientationNormalized of `alpha`) together with `_ha` (a_n = Pi^(-1)). These are the same
  hypotheses as in the landed parent's FiniteLevels. OK.
* "Q_K in C_X" is `hQ`, and "the (2a) projection map is invertible" is `hpf` on the actual
  `SpTowerShriek.projection`. Both hold for every K. OK.
* h_K is `projectionCounit` = F(sigma) ≫ PF^-1 ≫ sigma ≫ 1⊗counit ≫ right unitor, which is
  the step-1 formula. t_K is `tensorMate` = adj.homEquiv h = G(h) ∘ eta. g_K is `gamma` =
  (1⊗a) ≫ t, and tau is absorbed into the ordered presentation `source`. OK.
* The three naturality conjuncts, for h, t and g, quantify over all K, L and v : K ⟶ L in
  the tower category. OK.
* (h_K)_n: the evaluated `originalComposite` equals the inverse hom-equivalence of
  `intrinsicTheta`. Since theta is the transpose of h_fin, this is h_fin. OK.
* (t_K)_n = theta is `WordComparison … tensorMate finiteTheta`, and
  (g_K)_n = gamma is `WordComparison … gamma (FiniteSmoothPurity.gamma … alpha …)`. OK.

Edge cases: d = 0, n = 0, ramified e > 1, K = 0, empty X or Y, and non-normalized towers are
all covered. There is one universe u.

Change made (owner of theta): `finiteTheta` still called `Etale.smoothTensorDualityMap`. That
is a plain def owned by the theorem node thm-asd-smooth-tensor, which is not a statement
dependency. It now uses `Etale.FiniteSmoothPurity.gamma` at the identity orientation
`Iso.refl` of the dualizing complex (def-pur-finite-smooth-canonical-maps), which already
supplies the finite gamma of the statement. Its value is (1 ⊗ 𝟙) ≫ smoothTensorDualityMap,
the same map. This is the fix already given on b34c. The statement text is unchanged.

Advisories:

* The def owners SpTowerP1.*, SpCoordinateAdjunction.*, SpChartAdmissibility.Twists and
  FiniteSmoothPurity.* are not cited, the same as for the parent.
* Import cycle. det-sp-tower-gamma lists this item as a proof dependency, but this module now
  imports SmoothPurityTowerGamma. Its module therefore cannot import this one: by
  stages/2-statements.md §7 that import is left out and listed. Stage 3 must split
  tower_gamma or the shared definitions to use this lemma.
* `dualizingWord` inserts f^!(smoothPurityUnitIso.inv); stage 3 relates it to `_ha`'s unit
  identification.

Compile: I compiled the fixed module alone with `tools/nt_compile.py --json` against the live
library (see the maintainer review record).
