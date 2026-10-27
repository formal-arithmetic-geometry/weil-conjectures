## Worker report

The delivery states `AlgebraicGeometry.ProEtale.SpTowerCalculus.compact_support_tower_reduction`
in `Sheaf.Paper.CompactSupportTowerReduction`. Its only theorem has proof `sorry`.
No new construction, duplicate notion, dependency repair, or statement correction is needed.
The node is copied with only `lean` changed. The recorded signature is verbatim.

Source read: `literature/blueprint/latest/blueprint/sec-smooth-purity/` followed by
`sk-prop-sp-tower-geometric/sk-prop-sp-tower-geometric-gamma.proof.md`, paragraph (3).
This identifies compact-support reductions with finite compact support of the input
reduction following the canonical comparison b. The item's retained four-step proof
adds the uniform bounds from `det-sp-tower-bound-uniform`; its recorded finite-ring
constructible-origin and smooth-dimension hypotheses were also read. The current source
agrees with the item's compact-support assertion. There is no statement dispute.

Hypothesis and convention correspondence:

| Node text | Lean rendering |
| --- | --- |
| finite field k₀, characteristic p, algebraic closure k | `field : FiniteFieldDatum.{u}`; `field.k₀`, `field.p`, and `field.k` are the recorded global data. Its prime, cardinality, finite-field and algebraic-closure fields give these conditions. |
| prime ell different from p | `l : ℕ`, `[Fact l.Prime]`, `_hl : l ≠ field.p` |
| finite extension E of Q_ell | `E : Type u`, `[Field E]`, `[Algebra (Padic l) E]`, `[FiniteDimensional (Padic l) E]` |
| valuation ring and chosen uniformizer | the dependency's actual `Padic.coefficientExtensionIntegers l E` and `Padic.coefficientExtensionUniformizer l E` occur through the recorded base and coefficient rings |
| ell = unit times uniformizer^e, e ≥ 1; R_n = A_(E,en) | `base : SpTowerShriek.Base l E` carries `ramification`, `ramification_positive`, `ramificationUnit`, `ramification_eq`, `ideals`, and positive-quotient finiteness. `SpTowerShriek.R l E n` is O_E/(ell)^(n+1). Index n in Lean is positive exponent n+1 in the node. |
| X,Y separated finite-type k-schemes | `[X.Over (Spec (.of field.k))]` and its Y counterpart; `IsSeparated`, `LocallyOfFiniteType`, `QuasiCompact` for each structure morphism |
| f a k-morphism, separated, smooth of pure relative dimension d ≥ 0 | `f : X ⟶ Y`, `[f.IsOver (Spec (.of field.k))]`, `[IsSeparated f]`, `d : ℕ`, `[SmoothOfRelativeDimension d f]`. Smoothness and finite type follow from these hypotheses and the finite-type source/target. |
| ordinary derived strict towers, actual level evaluations and reduction maps | `q : Coordinates l E base` gives the section-preserving abelian interfaces and adjunction-normalized scalar coordinates. `C l E base q X`, `spDerivedCoefficientEvaluation`, and `reduction` use precisely those existing interfaces. |
| C belongs to the uniform constructible finite-Tor full subcategory, without normalization | `K : C l E base q X`; this is `spConstructibleTorTowerCategory`, with `K.property` the uniform predicate. No `IsSpNormalizedTower` or invertibility assumption occurs. |
| choose a compactification f = pj | `c : Compactification f`, with actual open `c.i`, proper `c.g`, and the bundled factorization equality |
| compute F = Rp_* j_! | `F l E base ops q c` is the recorded composite transported from the section model to the original strict tower category; `ops : SpTowerShriek.Operations l E base` supplies its actual geometric operations. |
| finite units/counits, twists, dualizing tower, and levelwise pullback | These fix the ambient conventions, but do not occur in either asserted formula or bound. Their recorded modules are imported. No arbitrary G, omega, twist, or pullback is substituted into the conclusion. |

Conclusion correspondence:

1. `∃ v : ∀ n : ℕ, Evaluation l E base ops q c n` supplies the natural finite
   evaluations. `Evaluation.normalization` fixes each comparison to the specific
   `SpTowerShriek.Fcomparison` and exact-localization coordinate words; this is not
   an unconstrained isomorphism.
2. The first conjunct, for every `m n` and `h : m ≤ n`, is the node's reduction
   factorization with its evaluation identifications written explicitly. Its left
   side is scalar extension of the evaluation at n, followed by
   `reductionDirectImageComparison (quotient l E h) c.i c.g`, followed by
   `reductionCompactSupport ... .map` of the input's canonical `reduction`.
   Its right side is the actual output tower's canonical reduction followed by
   evaluation at m. This is exactly rho^(FK) = F_m(rho^K) composed with b after
   conjugating by finite evaluations. The b definition is the normalized proper
   exchange followed by the extension-by-zero tensor comparison.
3. The second conjunct is the equal-index law: actual output reduction equals
   `scalarUnit ... .hom.app` of the output level. Thus it is identity under the
   canonical tensor-unitor identification, including the first positive level.
4. The third conjunct quantifies all `r ≤ m ≤ n`. Scalar extension of the first
   reduction followed by the next equals `scalarAssoc ... .hom.app` followed by
   the direct reduction. It includes equalities of any or all indices and uses the
   dependency's canonical derived tensor associator.
5. The fourth conjunct is `spConstructibleTorTowers` of the actual output object,
   exactly membership in the uniform unnormalized category C_Y.
6. The last conjunct quantifies every common input Tor interval `[a,b]` with
   `a ≤ b`. For each level it asserts `spFiniteConstructibleTor` of the output,
   `HasProEtaleTorAmplitude ... a (b + 2 * (d : ℤ))`, and
   `cohomologicalInterval ... a (b + 2 * (d : ℤ))`. The latter means every
   cohomology outside that same interval is zero. The endpoints are chosen once,
   before quantifying n, so the bounds are coefficient-independent. There is no
   flatness or finite-projective-dimension hypothesis on any quotient.

Dependency declarations read and reused:

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing`, publicly importing the actual integers,
  uniformizer and coefficient-ring definitions.
- `def-weil-scheme-morphism-properties` has a convention record, not a declaration;
  its listed Mathlib scheme properties are used directly.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `Smooth`, `SmoothOfRelativeDimension`;
  `Mathlib.AlgebraicGeometry.Morphisms.Etale`: the smooth-dimension permanence API.
- `Sheaf.Paper.SmoothPurityCoefficientTowers`: `spCoefficientTowers`, `spEllIdeal`,
  `spCoefficientRings`, with the actual quotient-semilinear transitions.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory` and its standard localization.
- `Sheaf.Paper.SmoothPurityNormalizedTowers`: `spDerivedCoefficientTowers`,
  `spDerivedCoefficientEvaluation`, `spFiniteConstructibleTor`,
  `spConstructibleTorTowers`, `spConstructibleTorTowerCategory`.
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor`:
  `AlgebraicGeometry.ProEtale.derivedTensor`, the recorded ordinary K-flat tensor.
- `Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted`: the recorded
  `WeilConjectures.sfIntegralTwistingFunctor`, `sfRationalTwistingFunctor`,
  `sfQbarTwistingFunctor`, retained as ambient conventions.
- `Sheaf.Paper.SmoothPurityTowerGluing`: `SpTowerGluing.tower_gluing`, `support`,
  `level`, `Levels`; its public interface supplies the exact same tower coordinates.
- `Sheaf.Paper.DerivedPullbackTensorHom`: `WeilConjectures.finiteDerivedPullback`,
  `finiteIntrinsicDerivedTensor`, fixing the levelwise ordinary operations.
- `Sheaf.Paper.SmoothPurityCoefficientTowersAbelian`: `SpCoefficientTowersAbelian`,
  its exact evaluations, `reduction`, `reduction_rep`, `reduction_identity`,
  `reduction_comp`, and `sp_coefficient_towers_abelian`.
- `WeilConjectures.Compactification.RefinementCategory`: `Compactification.Refinement`
  and `Compactification.category`, using the existing `Compactification` bundle.
- `Sheaf.Paper.SmoothPurityTowerShriekLevels`: `SpTowerShriek.Base`, `Operations`,
  `F`, `Fcomparison`, `R`, `tower_shriek_levels`.
- `Sheaf.SecSmoothPurity.ReductionDirectImage`: `reductionDirectImage_isIso`,
  `reductionDirectImage_cocycle`; the imported comparison module defines the actual
  `reductionDirectImageComparison` and `reductionCompactSupport` used here.
- `Sheaf.Paper.CompactSupportUniformTorBound`: `compactSupport_uniform_tor_bound`.
- `Sheaf.Paper.FiniteRingConstructibleDerivedOrigin`:
  `AlgebraicGeometry.Scheme.finiteRing_constructibleDerived_origin`.
- `Sheaf.Paper.CoefficientTowerShriekCalculus` and its public interfaces:
  `coefficient_tower_shriek_calculus`, `Coordinates`, `C`, `F`, `Evaluation`,
  `quotient`, `reduction`, `scalarUnit`, `scalarAssoc`, `cohomologicalInterval`,
  `ReductionCalculus.reduction_formula`. The last is a general constituent of the
  theorem, but does not include this item's unconditional smooth output bounds;
  it is reused, not duplicated as a private definition.

Searches (2026-10-25):

- `msearch.py`, LeanFinder: "Reduction maps of compact support direct image on strict
  coefficient towers factor through coefficient base change with uniform Tor bounds".
  Eight hits: `IsBaseChange.of_comp`, `IsBaseChange.comp`, `IsBaseChange.comp_iff`,
  `KaehlerDifferential.moduleBaseChange'`, `IsBaseChange.finitePow`,
  `AdicCompletion.tensor_map_id_left_eq_map`,
  `Algebra.Generators.H1Cotangent.map_comp_cotangentComplex_baseChange`,
  `Algebra.Generators.H1Cotangent.δAux_ofComp`. None states this theorem.
- `msearch.py`, Loogle, `"LowerShriek"`: zero hits.
- `msearch.py`, Mathlib grep,
  `compactSupportTower|reduction.*[Ll]owerShriek|torAmplitude.*[Ll]owerShriek`:
  zero hits.
- Source searches in `lean/WeilConjectures` and `lean/Sheaf` for the node id,
  `compactSupportTowerReduction`, `compact_support_tower_reduction`,
  `reduction_formula`, and `compactSupport_uniform_tor_bound`: no existing declaration
  combines the item's clauses. Found the recorded reduction formula and bound theorem,
  and the item citation in `SmoothPurityTowerGamma.lean`; these are dependencies or
  consumers, not a second existing statement of this item.

Edge cases checked before drafting: exponent one is index zero, never omitted;
`m=n` and all triple-index coincidences are included by non-strict inequalities;
`d=0` gives precisely `[a,b]`; empty schemes and empty geometric fibres require no
point or nonemptiness witness; zero towers satisfy all intervals and remain zero;
negative integer endpoints are allowed; unnormalized towers (including zero
transitions) remain in the domain. No assumption that rho^K is invertible appears.
All universes and variables are explicit (`set_option autoImplicit false`), and
coefficients and schemes share the established dependency convention without
identifying site object and morphism universes (these remain u+1 and u).

Validation: `scompile.py Q07 lem-sp-compact-support-tower-reduction` compiled the
sandbox file and its library-path form successfully (8.6 s and 7.4 s). No errors
or non-sorry warnings. The file has no lines over 100 characters. Delivery preflight
and its per-file compile are run through `deliver2.py --no-push` before pushing.

## Second reading by Q07

Independent reading by the maintainer reviewer (cc review service, 2026-10-25) of delivery
c1318a99. The worker's section above is a self-audit. This section replaces the
dispatcher placeholder. The Lean module and the `lean` record are unchanged.

Node statement, item by item, with its Lean rendering and verdict:

1. k₀ finite of characteristic p, k = algebraic closure: `field : FiniteFieldDatum.{u}`
   (fields `p`, `prime`, `k₀` finite, `k` with `IsAlgClosure k₀ k`). OK.
2. ℓ prime, ℓ ≠ p: `l`, `[Fact l.Prime]`, `_hl : l ≠ field.p`. OK.
3. E/Q_ℓ finite, O_E, ϖ_E, ℓ = uϖ^e with e ≥ 1, R_n = O_E/ℓ^n = A_{E,en}: `E` with
   `[FiniteDimensional (Padic l) E]`. `SpTowerShriek.Base` carries `ramification`,
   `ramification_positive`, `ramificationUnit`, `ramification_eq` (in the actual
   `coefficientExtensionIntegers`) and `ideals : spEllIdeal^(n+1) = coefficientExtensionIdeal (e(n+1))`.
   `SpTowerShriek.R l E n` = O_E/ℓ^(n+1). The node's index n ≥ 1 is the Lean n+1,
   the det-sp-tower-shriek-levels convention. Level 1 is Lean index 0, so no level is dropped. OK.
4. X, Y separated finite-type k-schemes: `Over`, `IsSeparated`, `LocallyOfFiniteType`
   and `QuasiCompact` of each structure morphism. OK.
5. f smooth separated of pure relative dimension d ≥ 0: `f.IsOver`, `[IsSeparated f]`,
   `d : ℕ`, `[SmoothOfRelativeDimension d f]` (def-sbc-smooth-morphisms record). OK.
6. Ordinary derived strict towers, C_T, evaluation: `spDerivedCoefficientTowers`,
   `spDerivedCoefficientEvaluation`, `C l E base q T` = `spConstructibleTorTowerCategory`
   (sk-def-sp-normalized-towers). No `IsSpNormalizedTower` is assumed. OK.
7. ρ^C_{n,m}: `reduction l E X (q.abelian X) h (q.scalar X h)`. This is the
   det-sp-coefficient-towers-abelian reduction transported by the adjunction-normalized
   `ScalarCoordinates.scalar`. Its `unit` field pins it, so no free automorphism remains. OK.
8. Compactification f = pj and F = Rp_* j_!: `c : Compactification f`,
   `F l E base ops q c` = realization ⋙ `SpTowerShriek.F` (openD (openOp c.i) ⋙
   push (geometry c.g)) ⋙ realization⁻¹. This is det-sp-tower-shriek-levels' functor. OK.
9. Finite evaluations: `∃ v : ∀ n, Evaluation …`. `Evaluation.normalization` pins
   `comparison.hom` to levelComparison⁻¹ ≫ counit ≫ `Fcomparison` ≫ Rf_!(levelComparison).
   So the existential is not a free choice. OK.
10. ρ^{FC}_{n,m} = Rf_{!,R_m}(ρ^C_{n,m}) ∘ b_{R_n,R_m}(C_n) for 1 ≤ m ≤ n: conjunct 1.
    LHS = scalarExt(v_n) ≫ `reductionDirectImageComparison (quotient h) c.i c.g` ≫
    `reductionCompactSupport R_m`.map(ρ^C), and RHS = ρ^{FC} ≫ v_m. The typing and
    orientation match. The conjunct is literally `ReductionCalculus.reduction_formula` of
    lem-sp-coefficient-tower-shriek-calculus, with the same b (proper counit mate followed by
    the extension-by-zero identification, def-sp-reduction-direct-image-comparison). OK.
11. Identity indices and the quotient-composition cocycle: conjunct 1 at h = le_refl,
    conjunct 2 (ρ_{n,n} = scalarUnit) and conjunct 3 (cocycle through `scalarAssoc`, all
    r ≤ m ≤ n). These are the `reduction_identity`/`reduction_composition` forms applied to the
    output tower, as in proof step 4. OK.
12. F C ∈ C_Y: conjunct 4, `spConstructibleTorTowers` of the output. OK.
13. Common input Tor bounds [a,b] ⇒ levels constructible with common Tor and cohomology
    bounds [a, b+2d]: conjunct 5. The endpoints are fixed before ∀ n.
    `spFiniteConstructibleTor` ∧ `HasProEtaleTorAmplitude … a (b+2d)` ∧
    `cohomologicalInterval … a (b+2d)`. This is the same shape as det-sp-tower-bound-uniform
    (`compactSupport_uniform_tor_bound`, which also takes a ≤ b). OK.
14. No flatness or finite projective dimension of R_m over R_n: none is assumed. OK.

Edge cases: n = m (h = le_refl) is in conjuncts 1–3. Level 1 is index 0. d = 0 gives
[a,b]. Empty X or Y and empty fibres need no witness. Zero towers and zero or
non-invertible transitions stay in the domain. The `a ≤ b` premise only excludes the
empty interval, where the input levels vanish and the claim is trivial. That premise is
also the dependency's convention. Negative endpoints are allowed. Universes: schemes and
E share u, the site keeps u+1/u, and nothing is left unbound (autoImplicit false).

Arbitrary `base`, `ops`, `q`: all three structures pin their data by HEq/section and
adjunction-unit equations. The landed consumers (SmoothPurityTowerGamma,
SmoothPurityTowerReductionTranspose, compactSupport_uniform_tor_bound) quantify the same way.
The calculus' `reduction_transition_compatibility`, `reduction_identity_aux` and
`reduction_composition_aux` take arbitrary b, o, q. OK.

Searches: the worker's three kinds of search were repeated. Grep in lean/Sheaf and
lean/WeilConjectures for compact_support_tower_reduction and for reduction_formula
users found no existing declaration that combines the reduction formula with the
unconditional smooth output bounds. `ReductionCalculus.reduction_formula` is a field of
the calculus structure, under a Preservation hypothesis and without the bounds, so it is
a dependency and not a duplicate.

Advisory (no change): the statement uses declarations owned by definition nodes that are
not in stmt_deps. These are def-sp-coefficient-tower-shriek-interfaces (Coordinates, C,
F, Evaluation, quotient, reduction, scalarUnit, scalarAssoc, cohomologicalInterval),
def-sp-reduction-direct-image-comparison (b), det-sp-scalar-extension-functor,
def-weil-proetale-tor-amplitude and def-nagata-compactification. The stmt_deps are
unchanged from the node. An S2 fix cannot add them, and the item cites no theorem node
for them. This matches the family precedent.

Changes: this report section only.
