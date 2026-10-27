## Worker report

The module `Sheaf.SixFunctors.IntegralDualExceptionalSystem` states the complete
ordinary derived strict-coefficient-system assertion of
`lem-coef-integral-dual-exceptional-system`. Its only theorem,
`WeilConjectures.IntegralDualExceptionalSystem.integralDualExceptionalSystem`,
has proof `sorry`. Every helper is a real composite or a structure specifying the
conclusions; no construction is chosen from an undetermined existence statement.
The item changes only in `lean`. There are no new nodes, dependency repairs,
statement corrections or disputed statements.

Hypotheses and objects, clause by clause:

- `D : FiniteFieldDatum.{u}` is the global finite-field datum, including the prime,
  finite base field and fixed algebraic closure. The binders `l`, `[Fact l.Prime]`,
  `hl : l ≠ D.p`, `E`, `[Field E]`, `[Algebra ℚ_[l] E]` and
  `[FiniteDimensional ℚ_[l] E]` express exactly the coefficient assumptions.
  The valuation ring, chosen uniformizer and finite quotients are those already
  used by `coefficientSequenceDerived`, with index `n : ℕ` denoting exponent n+1.
- `X Y : Scheme.{u}`, their `Over (Spec (.of D.k))` instances and the
  `LocallyOfFiniteType`, `QuasiCompact`, `IsSeparated` instances on both structure
  maps are the separated finite-type k-schemes. The same three conditions on `f`,
  together with `f.IsOver`, say it is the separated finite-type k-morphism.
  `c : Compactification f` is the prescribed open/proper factorization. The open
  immersion is quasi-compact because f is quasi-compact, as documented by the
  recorded `Compactification` declaration.
- `SX`, `SY`, `SZ`, `SS`, `r`, `g`, `aX`, `aY`, `βY`, `θ` are the specified
  system calculus and finite realization data supplied by the recorded
  `finiteAdjunctionDiagramRealization`. They introduce no integral comparison,
  preservation, amplitude or adjunction assumption. In particular `θ` is the
  specified system dual-formula comparison, not an arbitrary map between its
  finite evaluations. The symmetric structure is part of this recorded
  realization interface.
- `coefficientSequenceDerived l E W` is D(S_W), the ordinary unbounded derived
  category of strict semilinear module systems. `S.reduction`,
  `coefficientSequenceLimit`, `S.adjunction`, `coefficientSequenceInternalHom`
  and `coefficientIntegralInternalHom` are the recorded R, L, actual unit/counit,
  system internal Hom and ordinary ringed-site derived internal Hom. No second
  sequence category or internal-Hom construction is introduced.
- `aW.omega` is precisely the finite structural exceptional realization applied
  to the coefficient unit. `integralDual l E W aW.omega.obj` fixes the second
  argument of the existing internal-Hom bifunctor at its actual total limit.
  The dependency's `DualizingSpec` already identifies this limit and its same
  projections with `prop-coef-integral-dualizing`.
- `sfIntegralConstructibleCategory` is the actual Roos-complete constructible
  category with one common bounded cohomological support, with no separately
  assumed finite Tor condition. `firstDualPullback` is exactly
  L ↦ L_X f* R_Y D_Y L (the node's F); `doubleDualPullback` is exactly D_X F
  (the node's H). Both are actual functor composites. M is `integralDual` at L.

Conclusions, clause by clause (`Comparison` is the package returned, not a premise):

- `constructibleM`, `constructibleF`, `constructibleH` express all three integral
  constructibility clauses for every integral constructible L.
- `reductionX` and `reductionY` place every integral constructible reduction in
  the recorded normalized finite-Tor domain. In particular they assert the
  requested normalization at both W. The finite-Tor memberships are also what
  makes the expression E_f R_Y L well-typed; they are conclusions, never extra
  assumptions on L. `pullNormalized` is normalization of f* R_Y M.
  Normalization of E_f R_Y L follows directly from the codomain of `r.G`, namely
  `(domain l E X).FullSubcategory`, whose first property is normalization.
- `dualComparison` is beta followed by I(1,e_Ω), precisely as displayed in the
  node. `DualComparison.dualizingCounit` and `.invertible` assert the actual
  counit's and v's invertibility. `.naturality` is the contravariant naturality
  equation for v. `.evaluation` compares evaluation of v to
  `finiteDualComparison`: the evaluation-defined finite base-change Hom map,
  with the scalar reduction identifications and the evaluated actual dualizing
  counit. The latter's adjunct is the actual limit projection by the calculus's
  `counit_projection`. Thus this is the canonical dualizing coefficient map,
  not an unconstrained family of finite isomorphisms. `dualX` and `dualY` assert
  these clauses at both schemes and all integral constructible inputs.
- `completedCounit` asserts invertibility of precisely
  `SX.adjunction.counit.app (f* R_Y M)`. Naturality is already that of this actual
  counit natural transformation (restricted along the displayed functors).
  Its evaluated scalar-adjunction formula is exactly the recorded
  `SX.counit_projection`, available for every system, including this one.
- `q` is an isomorphism of contravariant system functors and `q_component` fixes
  its map to `qMap`, i.e. the actual completed-pullback counit followed by f*(v_Y).
  Thus q's inverse is the inverse of this very map.
- `b` is an isomorphism of covariant system functors on integral constructible
  objects. Its endpoints are R_X H and E_f R_Y L. `b_component` pins its map to
  v_X,F followed by D_X(q inverse) followed by theta inverse, with the
  contravariant direction explicit as `(q.inv.app (op L)).op`.
- `finite_component` is the equation in the actual finite derived category:
  evaluation of b followed by the prescribed exceptional evaluation equals
  evaluated v_X,F, the fiber-Hom identification, Hom of `finiteInverseQ` and
  the X dualizing identification, then the inverse finite dual-formula map.
  `finiteInverseQ` explicitly includes Y's inverse dualizing coefficient map,
  inverse fiber-Hom identification, inverse geometric pullback evaluation and
  evaluation of q inverse. Consequently both coefficient identifications and
  the finite dual-formula orientation are specified. Naturality and transition
  compatibility are intrinsic to b as an isomorphism of system functors, not
  reconstructed from a collection of level maps.
- `tor` quantifies over all integers a,b,dX,dY, with a≤b and dX,dY≥0. The dimension
  inequalities use `topologicalKrullDim` and `Int.toNat` only after the explicit
  nonnegative hypotheses; hence they express the given integer bounds without
  restricting any case. Every positive reduction of L has Tor amplitude [a,b]
  as premise; every reduction of the actual H has [a-2*dX,b+2*dY] as conclusion.
- No integral exceptional functor or integral exceptional adjunction is asserted.

Dependency declarations read and used:

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` and its public
  `CoefficientExtension` imports: `Padic.finite_coefficientExtensionRing`,
  `Padic.coefficientExtensionRing`, the ring of integers and uniformizer.
- `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`: the recorded completed
  coefficient sheaf and `integralConstantToCompletionOfUniverses` interface.
- `Sheaf.Paper.SfIntegralConstructible`: `sfIntegralConstructible` and its full
  subcategory; `Sheaf.Paper.DerivedCompleteOnSlices`: `IntegralOnSlice.IsComplete`.
- `Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction`:
  `scalarReductionDerivedExtension` (actual derived scalar extension).
- `Sheaf.Paper.CoefDerivedSystemEvaluationCalculus`:
  `CoefficientDerivedSystemCalculus`, `coefficientBaseChangeHom`, its
  `reduction`, `reductionEvaluation`, `adjunction`, `fiberHom`,
  `reduction_normalized`, `counit_projection` fields and canonical tensors.
- `WeilConjectures.Compactification.Defs`: `AlgebraicGeometry.Compactification`.
  The morphism-properties node is explicitly a convention node and has no
  declaration; its listed Mathlib `LocallyOfFiniteType`, `QuasiCompact`,
  `IsSeparated`, `Over`, `IsOver` are used directly.
- `Sheaf.SixFunctors.FiniteAdjunctionDiagramRealization`:
  `FiniteAdjunctionDiagram.Realization`, `Geometry`, `DualizingOperation`,
  `DualizingOperation.omega`, `.finiteOmega`, `Duality`, `dual`, `domain`,
  `evaluation`, `reducedConstructible`, and `Geometry.pullEvaluation`.
- `Sheaf.SixFunctors.IntegralDualizing`: `prop_coef_integral_dualizing` and
  `integralDualizingFiniteTerm`, with `DualizingSpec` retaining its projections.
- `Sheaf.Algebra.Homology.OrdinaryModuleDerivedInternalHom` publicly retains
  `CategoryTheory.derivedInternalHomOfUniverses`; this is precisely the
  ringed-site Hom used by `coefficientIntegralInternalHom`. Its ordinary-module
  specialization is not substituted for sheaf modules.
- `Sheaf.Paper.DerivedPullbackTensorHom`: `finiteDerivedPullback`.
- `Sheaf.Paper.IntegralDerivedOperationsOnSlices` publicly retains the integral
  operations; F is the node's literal system total-limit formula, rather than
  an unrelated pullback with the same finite objects.
- `Sheaf.Paper.FiniteTorAmplitudeSites` publicly retains
  `HasProEtaleTorAmplitude`, `finiteTorConstructible` and the integral predicate.
- `Mathlib.Topology.KrullDimension`: `topologicalKrullDim`.
- Stated proof dependencies are imported privately: `IntegralResidueTor`,
  `CoefficientSystemDerivedComparison`, `IntegralOperationsPreserveConstructible`,
  `PurNormalizedReconstructionAdjunctionCalculus`, `PullbackTorAmplitude`,
  `ExtensionIntegersDvr`, `IntegralVerdier`. The coefficient completeness leaf
  is Mathlib `spectralNorm.completeSpace` in
  `Mathlib.Analysis.Normed.Unbundled.SpectralNorm`, available through the existing
  coefficient imports (there is no separate project module for that leaf).

Edge cases checked before writing: n=0 means exponent one, with no omitted finite
level; arbitrary ramified finite coefficient extensions are allowed. Zero objects
satisfy every ordered Tor interval. Empty schemes have dimension bottom and permit
dimension bound zero. No nonempty hypothesis, smoothness, properness of f,
uniform Tor hypothesis on arbitrary normalized systems, or integral exceptional
adjunction has been introduced. For the identity of a point with dX=dY=0 the
output interval is exactly [a,b]. Applying the two dual bounds gives
[-(-a)-2dX,-(-b-2dY)]=[a-2dX,b+2dY], confirming the signs. q inverse has source
f* D_Y R_Y L and target R_X F; contravariance therefore gives the displayed
D_X R_X F → D_X f* D_Y R_Y L.

Searches (2026-10-24):

- `msearch.py ... leanfinder "Integral Verdier dual completed pullback dual coherent
  finite exceptional inverse image system comparison"`: 8 hits, ordinary sheaf
  pullback comparisons such as `SheafOfModules.pullbackComp`, `.pullbackIso`,
  `.conjugateEquiv_pullbackComp_inv`; none states this system assertion.
- `msearch.py ... leansearch "Integral dual pullback dual normalized coefficient
  systems exceptional inverse image comparison"`: 8 hits, general pullback
  comparisons, dual-basis coefficients and normalization of schemes; no match.
- `msearch.py ... loogle '"verdier"'`: 12 hits concerning Verdier localizing
  subcategories; no coefficient-system comparison.
- `msearch.py ... grep 'verdierDual|exceptionalInverseImage|upperShriek'`: zero
  Mathlib hits. Project/source rg for `integralDualExceptional`,
  `dualExceptionalSystem`, and the item id found no existing declaration.
  The existing generic Hom, finite dual functors and system calculus were reused.
- Read the newest `literature/blueprint/latest/` (symlink main-20261024). The
  node's historical paragraph filename is no longer present in that reorganized
  source. The current `sec-six-functors/sk-thm-sf-kunneth-verdier/`
  `thm-sf-ctf-stability.md`, clause (v), and its proof confirm the finite formula
  and interval. The accepted node and its complete eight-step proof supply the
  specific ordinary-system assertion being formalized; no historical snapshot
  was opened and no different condensed category was substituted.

Validation: all compilation uses the authorized `scompile.py` wrapper; no build or
edit of the shared repository is performed. The initial compile diagnosed an extra
inferred-argument call to `finiteInverseQ`; removing the two unused call arguments
corrected it. Final compile and delivery preflight results are recorded below.

## Second reading by Q90

The delivered section with this heading was the worker re-reading its own work ("the
author's explicit second pass, not a claimed independent review"). The maintainer's
reviewer replaced it with the independent clause-by-clause reading below (review of
12226ef39cb1, 2026-10-24). The Lean module and the node record are unchanged.

Objects and hypotheses, the Lean that renders each, and the verdict:

1. k = F̄_q, ℓ ≠ p, E/Q_ℓ finite, R, ϖ, A_n: `D : FiniteFieldDatum.{u}` (field k with
   `IsAlgClosure k₀ k`, |k₀| = q), `l`, `[Fact l.Prime]`, `hl : l ≠ D.p`, `E` with
   `[Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]`; the quotients are the recorded
   `Padic.coefficientExtensionRing l E (n+1)`, index n meaning exponent n+1. Exact.
2. X, Y separated finite type over k; f separated finite type over k; f = pj:
   `Over (Spec k)` with `LocallyOfFiniteType`, `QuasiCompact`, `IsSeparated` on both
   structure maps and on f, `f.IsOver`, `c : Compactification f`. Exact, no extra hypothesis.
3. S_W, R_W ⊣ L_W, u, e, H_W, I_W of the system calculus: `SX SY : CoefficientDerivedSystemCalculus`,
   `S.reduction`, `S.adjunction` (actual counit), `coefficientSequenceInternalHom`. They are
   arbitrary calculi without the `Coherence` package: the conclusions only use
   `reduction_normalized`, `isIso_iff_evaluations`, `beta_evaluation`, `counit_projection`
   and `fiberHom`, which every calculus carries, and
   `purNormalizedReconstruction` holds for an arbitrary calculus. So this is a harmless
   generalization, not a stronger hypothesis.
4. F_f, E_f, Ω_W, D_W, θ of lem-coef-finite-adjunction-diagram-realization: `r : Realization`,
   `g : Geometry`, `aX aY : DualizingOperation`, `βY`, `θ : Duality r aX aY βY g`, exactly
   the data of that theorem's existential. `aW.omega = E_{a_W}(unit)`; `dual W Ω` is
   I_W(−,Ω); `θ.iso : r.G ⋙ ι ≅ ι ⋙ dualFormula`, where `dualFormula` is D_X f^* D_Y with
   the system pullback `integralComparisonDerivedSequencePullback`. θ is pinned at every level
   by `θ.finiteFormula` against `FiniteExceptional.dualFormulaIso`. Exact.
5. ω_{W,R} = L_WΩ_W, D_{W,R}P = RHom_{R_W}(P, ω_{W,R}): `integralDual W Ω` is the flip of
   `coefficientIntegralInternalHom` (ringed-site `derivedInternalHomOfUniverses` over the
   completed ring sheaf) at `coefficientSequenceLimit Ω`. `aW.dualizing : DualizingSpec`
   identifies this limit and its projections with prop-coef-integral-dualizing. Exact.
6. M = D_{Y,R}L, F = L_X f^* R_Y M, H = D_{X,R}F: `integralDual … (op L)`,
   `firstDualPullback` = integralDual ⋙ SY.reduction ⋙ system pullback ⋙ limit,
   `doubleDualPullback` = firstDualPullback.rightOp ⋙ integralDual X. These are literal
   composites, and the variance is correct. Exact.

Conclusions:

7. M, F, H are integral constructible: `constructibleM/F/H`, for all L in
   `sfIntegralConstructibleCategory`. Exact.
8. R_WP is normalized for integral constructible P: `reductionX/Y` give membership in N_W =
   `domain` (normalized, with finite-Tor constructible levels). This is what step 1 proves, and
   it is needed to type E_f R_Y L. f^*R_YM is normalized: `pullNormalized`. E_f R_Y L is
   normalized because it lies in the codomain of `r.G`. Exact.
9. v_{W,P} = I(1, e_Ω) ∘ β, natural iso, with its evaluation: `dualComparison` =
   `coefficientBaseChangeHom … ≫ IHom.map (𝟙, counit.app Ω)`. `DualComparison` asserts the
   dualizing counit is an iso, `invertible`, contravariant `naturality`, and `evaluation`
   (equal to `finiteDualComparison`, the finite base-change Hom with the scalar-reduction and
   evaluated-counit identifications). This holds at X and at Y. Exact.
10. e : R_XF → f^*R_YM is an actual counit iso: `completedCounit` is the IsIso of
    `SX.adjunction.counit.app (f^* R_Y M)`. Its naturality is that of the counit; its
    evaluation is the calculus field `counit_projection`. Exact.
11. q_L = f^*(v_{Y,L}) ∘ e: `q` is an iso of functors on (D^b_c(Y,R))ᵒᵖ, with
    `q_component : q.hom.app = counit ≫ f^*(dualComparison)`. It is pinned. Exact.
12. b_L = θ^{-1} ∘ D_X(q^{-1}) ∘ v_{X,F}: R_XH → E_fR_YL is a natural iso: `b` is an iso
    bSource ≅ reducedConstructible ⋙ r.G ⋙ ι, and `b_component` pins it. I checked the
    direction: q.inv.app : T → R_XF, its `.op` under `dual X` gives D_X R_XF → D_X T, and
    θ.iso.inv.app : D_X f^* D_Y R_YL → E_f R_YL. Exact.
13. Evaluations of b are the finite dual-formula maps, with both coefficient
    identifications: `finite_component`. I derived it from `θ.finiteFormula`, fiber naturality
    and IHom bifunctoriality: (P ≫ eval q^{-1}).op = eval(q^{-1}).op ≫ P.op, which is exactly
    `finiteInverseQ` with Y's `finiteOmega.inv`, the fiber-Hom inverse, the pullEvaluation inverse
    and eval(q.inv), followed by X's `finiteOmega.hom` and `dualFormulaIso.inv`. This is
    consistent with, and implied by, the dependency's identity. Exact.
14. Tor bound: `tor` quantifies over all integers a ≤ b and dX, dY ≥ 0, with
    `topologicalKrullDim W ≤ dW.toNat`. The premise is the Tor amplitude [a,b] of every
    reduction L_n (`scalarReductionDerivedExtension n`, which covers all n ≥ 1). The
    conclusion is [a−2dX, b+2dY] for every H_n. Exact.
15. "No integral exceptional adjunction is asserted": none is. Exact.

Edge cases: empty X or Y (Krull dimension ⊥ ≤ 0 is allowed); zero L (it satisfies any
interval); n = 0 is exponent 1, and no level is lost; the identity of a point with
dX = dY = 0 returns [a,b]; ramified E is allowed. Universes: everything is at Scheme.{u},
E : Type u, D : FiniteFieldDatum.{u}, the same as the realization dependency.

One definition per notion: the item introduces no new notion. The helpers are composites
of recorded declarations, or the conclusion structure. `rg` of the side lean tree finds no
existing integral dual-pullback-dual system comparison.

Maintainer advisory (not a fault): the statement uses declarations owned by nodes that are
not in stmt_deps. These are Realization, Geometry, domain, evaluation and
Geometry.pullEvaluation (def-coef-finite-adjunction-system-data); FiniteExceptional.dualFormulaIso
(lem-coef-finite-exceptional, `.choose` of its ∃!); the system pullback
(def-trf-integral-comparison-sequence-systems); and the sequence-site and calculus-data
notions. All of them are reached as interface types of the cited
lem-coef-finite-adjunction-diagram-realization and lem-coef-derived-system-evaluation-calculus,
which cite these nodes themselves, so the DAG order is preserved transitively. The chapter
convention is broad: about 60 landed users of the calculus cite neither def-coef-derived-system-calculus-data
nor def-coef-ringed-sequence-site.
