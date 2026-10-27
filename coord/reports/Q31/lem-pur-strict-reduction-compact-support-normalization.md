## Worker report

Group Q31, item `lem-pur-strict-reduction-compact-support-normalization`.
The module is `Sheaf.Paper.StrictReductionCompactSupportNormalization`, namespace
`AlgebraicGeometry.Scheme.StrictSupportNormalization`. It supplies the actual strict
compact-support arrow and specified corners, the normalization equality, and the
naturality, compositor, identity, refinement, common-refinement and exchange clauses.
All eighteen theorem proofs are `by sorry`; every definition has actual data.
No statement correction, new node, or dependency replacement is needed.

Source read: the current blueprint's
`sec-six-functors/sk-thm-sf-package/prop-pur-weil-equivariance-compatibilities.proof.md`,
constituent-compatibility paragraph, together with this node's nine proof steps and
its recorded dependency interfaces. The source is the compact-support base-change
constituent and compatibility under composition/refinement. The module docstrings
record the individual proof steps and Stacks references of the accepted split.

Hypotheses and clauses, in node order:

* Finite field, l different from p, the finite coefficient extension E and its integral
  ring: the main theorem takes `P : WeilConjectures.PurityFiniteSetting.{u}` and uses
  `P.coefficients.l`, `P.extension`, `PbcIntegralRing` and `pbcIntegralDatum` throughout.
  `arithmeticQuotient` and `arithmeticCompleted` select only the uniquely
  projection-normalized isomorphisms of
  `WeilConjectures.IntegralCoefficientPresentation.comparison`. `arithmeticInput`
  is actual derived scalar restriction along that completed-ring isomorphism.
  Thus the integral coefficients of the finite-Tor subcategory and of the adic datum
  are canonically identified, rather than assumed to be definitionally equal.
* Separated finite-type k-schemes X and Y: `X.Over`, `Y.Over`, and the
  `LocallyOfFiniteType`, `QuasiCompact`, `IsSeparated` instances on their structure
  maps. The specified f is over k and has the same three morphism properties.
* Arbitrary a and b: the main theorem's `g : Y' ⟶ Y`, `g' : X' ⟶ X` have no
  `IsOver` assumptions. `s`, `sp : ChosenCartesianSquare ...`, and
  `sj : OpenImmersionSquare ...` supply the proper/open pullback squares for c,c'.
  Iteration takes `h` in `kappaSource_composition` and `kappaTarget_composition`.
  Scheme maps on all these arrows remain arbitrary, so semilinear maps are included.
* Supplied compactifications: `c : Compactification f`, `c' : Compactification f'`
  use their actual open factors `c.i` and proper factors `c.g`. No replacement by
  unrelated proper/open functors is made. The source open is quasi-compact by
  `c.quasiCompact_openImmersion` from `[QuasiCompact f]`; its pullbacks are
  quasi-compact by the supplied open pullback square. No extra k-structure on Y'
  or Y'' is introduced.
* M in D^b_ctf: `K : finiteTorConstructibleIntegralCategory ... X`, the recorded full
  subcategory imposing bounded constructibility, derived completeness and one Tor
  interval for all positive quotient levels. The main theorem's `_origins` and
  `_openOrigins` are the supplied `PbcHasCompatibleEtaleOrigins` on M and j!M.
  These are exactly the intermediate witnesses mentioned in proof Step 2. Auxiliary
  coherence equations hold on the ambient category when they are formal equations;
  finite-origin invertibility/common-refinement clauses retain their witnesses.
* Actual strict quotient reduction and scalar restriction: `input d T` is
  `completedReductionTower T d ⋙ exchangeTowerRes d T`. It lives in a derived
  category of strict diagrams with the recorded quotient transition maps. The
  arithmetic exponent is n+1, enumerating every positive quotient, including P_1.
* The specified w_a: `exchange` is `d.towerV' sp` at j!K, followed by
  `d.towerPush c'.g` of the counit-normalized strict pullback presentation transport
  and `cbcOpenMateOmega d sj K`. Thus it uses the actual proper lift and strict
  finite open exchange, in the prescribed order. It is not an arbitrarily chosen
  isomorphism with the right endpoints and is not defined through an Rlim comparison.
* H_a: `ProEtale.StrictTower.compositionE` is the recorded proper square mate
  followed by the proper image of the unit-normalized open exchange. Its action on
  the displayed input is the right side of the main theorem after the source kappa.
* Specified kappa_s: `kappaSource` is `exchangeCornerB` followed by `G R` of
  `cbcRealizationQuotientOpen`; the latter is the same reduction/open tensor map
  followed by the normalized open scalar comparison. Specified kappa_t:
  `kappaTarget` is `exchangeResPush` followed by `R` of `cbcOpenMateB`, which retains
  the strict pullback/reduction and open-extension corners. Both are concrete isos.
* Normalization equation: `strictReductionCompactSupportNormalization` states
  `Res.map exchange ≫ kappaTarget.hom = kappaSource.hom ≫ compositionE.app input`.
  Lean's composition order is left-to-right; this is exactly the node's equation.
* Naturality: `kappa_naturality` gives both source and target equations for every
  morphism of ambient inputs; hence it restricts to the stated full subcategory.
* Compositors and identical intermediate corners: `modulePullComp` uses the actual
  coefficient compositor, `pullComp` its termwise derived descent, and `pushComp`
  its adjunction mate. `scalarPull_composition` and `scalarPush_composition` give
  their scalar compatibilities. `inputPull_composition`, `inputPull_identity`,
  `kappaSource_composition`, `kappaTarget_reduction`, and `kappaTarget_composition`
  state the resulting endpoint and intermediate-corner equalities explicitly.
  `targetComp` uses the same reduction corner and `d.pullComp`, rather than choosing
  new corners for the composite square. `kappaSource_reduction` fixes its source
  analogue. Together these are proof Steps 6--7 for a,b,ab, including identities.
* Strict refinement maps: `refinement` is the reduction of the recorded
  `cbcRefinementMap`, conjugated by the actual proper projection/open reduction
  isos. `refinement_normalization` carries it to the published
  `ProEtale.StrictTower.refinementComparison`. `sourceRefinement` and
  `targetRefinement` use the very same source/target reduction corners;
  `sourceRefinement_normalization` and `targetRefinement_normalization` state the
  equations under the same kappa_s,kappa_t as the exchange theorem.
* Identities, cocycle and exchange: `refinement_cocycle` states both equations;
  `refinement_exchange` states the actual restricted strict-arrow exchange square
  for a commuting pair of supplied refinements. `refinement_isIso` takes exactly
  the scalar finite-etale-origin domain used by the published constant comparison.
  `commonRefinement` uses its named invertibility result;
  `commonRefinement_normalization` identifies it with the normalized published
  comparison, and `commonRefinement_coherence` gives independence and the cocycle.
* Before inverse limit or evaluation: every equality is in derived strict diagram
  categories. Finite evaluation occurs only inside the finite-origin predicates.
  There is no Rlim functor in any newly defined arrow or equation and no appeal to
  faithfulness of evaluations. The site remains Scheme.{u} with coefficient carrier
  Type (u+1), not an imposed equality of site object and morphism universes.

Dependency declarations used (module and declaration):

* `def-pur-conventions`: `Sheaf.Paper.PurityFiniteSetting`, `WeilConjectures.PurityFiniteSetting`.
* `fix-lem-exchanges`: `Sheaf.Paper.ExchangeFunctoriality`, `WeilConjectures.exchangeFunctoriality`.
* `def-cbc-completed-exchange-map`: `Sheaf.Paper.CompletedCompactSupportExchange`, `AlgebraicGeometry.Scheme.completedCompactSupportExchange`.
* `def-weil-integral-rational-qbar-compact-support`: `Sheaf.Paper.QcqsCompactSupportRealization`, `WeilConjectures.sfQcqsCompactSupportRealization`.
* `lem-weil-pbc-strict-tower-exchange-mate-normalization`: `Sheaf.Paper.StrictTowerExchangeMateNormalization`, `AlgebraicGeometry.Scheme.strictTowerExchangeMateNormalization`.
* `lem-cbc-complete-proetale-refinement-exchange-coherence`: `Sheaf.Paper.RefinementExchangeCoherence`, `AlgebraicGeometry.ProEtale.StrictTower.refinementExchangeCoherence`.
* `def-weil-compactifications-refinements`: `WeilConjectures.Compactification.RefinementCategory`, `AlgebraicGeometry.Compactification.Refinement`.
* `pur713-def-base-changed-compactification`: `WeilConjectures.Compactification.BaseChange`, `AlgebraicGeometry.Compactification.ofIsPullback`.
* `def-weil-pbc-adic-coefficient-datum`: `Sheaf.Paper.AdicCoefficientDatum`, `AlgebraicGeometry.Scheme.completedReductionTower`.
* `lem-weil-pbc-constant-completion-equivalence`: `Sheaf.Paper.ConstantCompletionEquivalence`, `CategoryTheory.ConstantCompletion.equivalence`.
* `def-cbc-strict-constant-tower-operations`: `Sheaf.AlgebraicGeometry.StrictConstantTowerOperations`, `AlgebraicGeometry.ProEtale.StrictTower.Towers`.
* `def-cbc-strict-tower-open-extension`: `Sheaf.AlgebraicGeometry.StrictTowerOpenExtension`, `AlgebraicGeometry.ProEtale.StrictTower.J`.
* `def-weil-pbc-adjunction-mate`: `Mathlib.CategoryTheory.Adjunction.Mates`, `CategoryTheory.mateEquiv`.
* `lem-cbc-strict-tower-proper-open-calculus`: `Sheaf.AlgebraicGeometry.StrictTowerProperOpenCalculus`, `AlgebraicGeometry.ProEtale.StrictTower.normalizedProperOpenCalculus`.
* `def-weil-finite-tor-amplitude`: `Sheaf.Paper.FiniteTorAmplitudeSites`, `WeilConjectures.finiteTorConstructibleEtale`; the public re-export includes `finiteTorConstructibleIntegralCategory`.
* `lem-weil-pbc-integral-coefficient-presentation-comparison`: `Sheaf.Paper.IntegralCoefficientPresentationComparison`, `WeilConjectures.IntegralCoefficientPresentation.comparison`.
* `lem-weil-pbc-completed-ordinary-comparisons`: `Sheaf.Paper.CompletedOrdinaryComparisons`, `AlgebraicGeometry.Scheme.AdicCoefficientDatum.integralRingIso_comp`; also `AdicCoefficientDatum.pullComp` and `pullId`.

The strict proper normalization module also supplies `exchangeCornerB`,
`exchangeCornerD`, `exchangeResPull`, `exchangeResPush` and `exchangeTowerRes`;
`CompletedOpenStrictMateIdentification` supplies `cbcOpenMateOmega`,
`cbcOpenMateB` and the actual `cbcDatumTowerTransport`.
Its public realization helper interface supplies `cbcRealizationReduction`,
`cbcRealizationQuotientOpen` and `cbcRealizationTowerScalarOpen`, each used as a
canonical construction, not the downstream after-Rlim realization theorem.
The completed support/refinement arrows are `cbcSupport` and `cbcRefinementMap`.
Every proof-dependency module of the split is imported; the proof-only imports are
plain imports, and direct statement-dependency modules are public imports.
Three already landed nodes were added to stmt_deps for the finite-Tor category,
canonical integral coefficient presentation and ordinary pullback compositors.
No source or dependency statement was changed.

Edge checks: zero input and empty schemes are allowed (no nonempty binder).
Identity base change is covered by `inputPull_identity` and both compositor equations.
An identity open/proper factor still uses the original unit/counit comparisons.
No equidimensionality, smoothness, properness of f, or k-linearity of base change is
assumed. Positive quotient level one is n=0 in the tower. Refinements may have a
nonempty complementary clopen component: the actual mate retains the clopen
projector; it has not been replaced by an identity on the whole ambient scheme.
The independent common-refinement choices are quantified in the independence clause.

Searches actually run:

* msearch LeanFinder: "Strict quotient reduction compact support base change exchange
  normalized constant tower proper open mate with coherent scalar restriction corners".
  OK, eight unrelated supported-function/quasi-compact-scheme hits; no exact theorem.
* msearch Loogle: "CategoryTheory.mateEquiv, Functor.mapDerivedCategorySquareIso".
  OK, zero hits; the latter name is unknown. Follow-up `CategoryTheory.mateEquiv`
  returned twelve actual mates/composition declarations, used through Mathlib.
* msearch grep in Mathlib CategoryTheory:
  `Strict.*(CompactSupport|Normalization)|exchangeCorner`, zero hits; follow-up
  `exchangeCornerB|exchangeCornerD|StrictSupportNormalization`, zero hits.
* rg in lean/WeilConjectures and lean/Sheaf:
  `strict-reduction-compact-support-normalization|strictReductionCompactSupport|exchangeCornerB|exchangeCornerD`.
  Found the proper normalization and after-Rlim realization interfaces, but no
  compact-support normalization equation with all the stated coherence clauses.
* Exact item-id search in lean/WeilConjectures and name search
  `StrictSupportNormalization|strictReductionCompactSupportNormalization` in
  lean/WeilConjectures, lean/Sheaf and dag/lean_names_upstream.json: no declaration.

Compilation: prescribed scompile.py only. The module-mode sandbox and actual library
module compiled cleanly. Importing ExchangeFunctoriality exposed its exported chosen
IntegralHom derived-category instance; following that dependency's own pattern, the
module temporarily disables that instance during elaboration and restores it at the
end. This keeps the canonical instance and the original universe conventions.
No local instance, private definition, local notation, diagnostic #check, or data sorry.

## Second reading by Q31

Written by the maintainer's independent reader (review of ac2380d9), replacing the worker's
self-audit section. Both the node and `Sheaf/Paper/StrictReductionCompactSupportNormalization.lean`
were open, together with the modules of the recorded dependencies (side-live clone).

Node clauses and the Lean that renders them:

1. Conventions of def-pur-conventions, R = O_E, P_n = R/ϖ^n, completed sheaf. Lean:
   `P : PurityFiniteSetting.{u}`, `pbcIntegralDatum P.coefficients.l P.extension`; tower index
   n ↦ R/ϖ^(n+1), so every positive quotient P_1, P_2, … appears. The finite-Tor category lives over
   the completed constant-sheaf ring, the adic datum over the Cont(π₀) presentation;
   `arithmeticInput` restricts scalars along the unique projection-normalized e_T of
   `IntegralCoefficientPresentation.comparison` (`arithmeticQuotient` = the unique e_n,
   `arithmeticCompleted` = the unique e_T). Canonical, not arbitrary. Correct.
2. f separated finite type between separated finite-type k-schemes. Lean: `X.Over`, `Y.Over`
   with LocallyOfFiniteType + QuasiCompact + IsSeparated of the structure maps;
   `[f.IsOver]`, `[IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]`. Correct, nothing stronger
   (no properness of f, no smoothness).
3. a, b arbitrary scheme maps (semilinear allowed). Lean: `g : Y' ⟶ Y`, `g' : X' ⟶ X` with no
   IsOver; `h` in the compositor clauses. Correct.
4. Compactification c = (j, p) and its pullbacks. Lean: `c : Compactification f`, `c'` with
   `sp : ChosenCartesianSquare s c'.g c.g g` and cartesian `sj : OpenImmersionSquare g' c'.i c.i s`,
   the same interface as `completedCompactSupportExchange` (def-cbc-completed-exchange-map).
   Correct (base-changed compactification up to the supplied cartesian squares).
5. Open factors quasi-compact. From `[QuasiCompact f]` via `c.quasiCompact_openImmersion`, and by
   base change. Correct.
6. M ∈ D^b_ctf(X, R) with compatible finite étale-origin witnesses. Lean:
   `K : finiteTorConstructibleIntegralCategory`, `_origins` on M and `_openOrigins` on j_!M
   (`PbcHasCompatibleEtaleOrigins`, owned by def-weil-pbc-bounded-constructible-complete), as in
   proof Step 2. Correct.
7. 𝓡_T and Res_T. Lean: `input d T = completedReductionTower T d ⋙ exchangeTowerRes d T`, in the
   derived category of strict diagrams with quotient transitions. Correct.
8. w_a = proper strict lift v' followed by the strict finite open exchange. Lean: `exchange` =
   `d.towerV' sp (j_!K)` (the v' that `completedExchange` takes Rlim of) then `towerPush c'.g` of
   the pullback-presentation transport and `cbcOpenMateOmega` (actual strict exchange conjugated by
   ρ_j). Same order as def-cbc-completed-exchange-map. Correct.
9. H_a^T = (R_{p_a} β_a)(E_{p,a} J_j). Lean: `ProEtale.StrictTower.compositionE` =
   whiskerLeft J (exchange mate) ≫ whiskerRight β R; I read its definition. Correct.
10. κ_{a,s}, κ_{a,t}. Lean: `kappaSource` = `exchangeCornerB` (the b of the proper normalization)
    then G R (z_j = `cbcRealizationQuotientOpen`); `kappaTarget` = `exchangeResPush` then R of
    `cbcOpenMateB`. These are the node's Step 3 and Step 4 corners. Correct.
11. κ_t ∘ Res(w_a) = H ∘ κ_s. Lean: `strictReductionCompactSupportNormalization`, written in
    diagrammatic order, and the same equation. Correct.
12. Naturality: `kappa_naturality` (both corners, any morphism). Correct.
13. a, b, ab corners intertwine the pullback compositors, and the intermediate corners are identical.
    Lean: `pullComp`/`pushComp` (actual coefficient compositor and its mate),
    `scalarPull_composition`, `scalarPush_composition`, `inputPull_composition`, `inputPull_identity`,
    `kappaSource_composition`, `kappaTarget_composition` (with `targetComp`). `kappaSource_reduction`
    and `kappaTarget_reduction` express both corners through the same `supportScalar` and reduction
    maps, so the target of one substitution is the source of the next. Correct.
14. Refinements go to the normalized constant comparisons, with the cocycle and exchange
    intertwining. Lean: `refinement` (the reduction of `cbcRefinementMap` conjugated by the projection
    and open reduction isos), `refinement_normalization`, `source/targetRefinement_normalization`,
    `refinement_cocycle`, `refinement_exchange` (same orientation as the exchange clause of
    `refinementExchangeCoherence`), `refinement_isIso`, `commonRefinement` (inverse only through
    that named theorem), `commonRefinement_normalization`, `commonRefinement_coherence`. Correct.
15. Before Rlim or evaluation, semilinear, no k-linearity: no Rlim appears in any new arrow;
    evaluation appears only inside the origin predicates. Correct.

Edge cases: M = 0 and empty schemes are allowed (no nonemptiness binder). a = id is covered by
`inputPull_identity`. j = id still uses the unit-normalized maps. Identity refinement is in
`refinement_cocycle`. A refinement with nonempty complementary clopen keeps its projector through
`cbcRefinementMap`. Universes: Scheme.{u}, coefficients Type (u+1); no equality is forced.

Theorem stmt_deps: lem-weil-pbc-integral-coefficient-presentation-comparison supplies the unique
e_n, e_T as `.exists.choose` of its ∃! conclusions. lem-weil-pbc-completed-ordinary-comparisons
supplies `d.pullComp` (eqToIso of `integralRingIso_comp`) and `d.pullId` (`modulePushId`, which is
the choose of `modulePushId_existsUnique`). These are objects constructed by the theorems, so the
statement genuinely needs them.

Searches (reader): rg in lean/Sheaf and lean/WeilConjectures for `towerPull (h ≫ g) ≅`,
`IntegralCoefficientPresentation.comparison`, `integralDetailedTransport` and `compositionE`. The
only near-duplicate is `PurIntegralTower.pullComp`/`pushComp` in the theorem-node module of
lem-pur-isomorphism-strict-integral-exchange-normalization (same body). It cannot be cited without
another theorem stmt_dep, so this is advisory only.

Mismatches found: none in substance. Advisory notes for the maintainer: several defining owners
are used but not in stmt_deps: def-sf-completed-open-strict-mate-data,
def-cbc-strict-tower-composition-maps, def-sf-strict-exchange-realization-corners,
def-sf-completed-compact-support-calculus-data, def-cbc-completed-open-scalar-quotient-interface and
def-cbc-completed-pullback-counit-transport. Only this report was changed.
