## Worker report

The delivery defines `AlgebraicGeometry.Scheme.QuotientFrobenius.quotientCornerFrobeniusStructures`
in `Sheaf.Paper.QuotientCornerFrobeniusStructures`. It constructs the displayed structures
from one coherent Weil isomorphism on the derived ringed quotient sequence site. No node
statement, dependency record, target, or upstream source is changed. All theorem proofs are
`sorry`; definitions contain actual data, or choose universal derived pairs and comparisons
whose normalization equations determine them. The normalization properties are named theorems
with source and complete natural-language construction arguments in their docstrings.

### Hypotheses and clauses

| Node clause | Lean rendering |
| --- | --- |
| Adic datum A,I and positive perfect finite quotients | `d : AdicCoefficientDatum A`, its `ideal`, `quotientFinite`, `finiteRing`, `completedRing` and `projection`; n denotes exponent n+1, including n=0. |
| The specified proper Cartesian square | `sq : ChosenCartesianSquare g' f' f g` and `[IsProper f]` in `finiteTheta` and the main construction. |
| Derived-complete K | `K : d.derived X` and `hK : d.TowerComplete X K`. Most formulas extend to ambient K; the main constructor retains the required hypothesis. |
| Individual finite etale-origin witnesses | `W : ∀ n, FiniteEtaleOriginWitness X (A ⧸ d.ideal ^ (n+1)) ((d.reduction X n).obj K)`, passed to the published `d.fourArrows sq K hK W n`. There is no uniform lower bound or additional compatibility hypothesis. |
| Exactly the four quotient corners and arrows | `d.fourCorners` and `d.fourArrows`, without new copies. |
| Exactly the ambient strict corners, H and H' | `d.fourTowerCorners`, `d.towerH`, `d.towerH'` from the recorded normalization module. |
| Automorphisms, commutations, coherent Cartesian cube | `Cube sq` contains four scheme isomorphisms and all four commutation equalities; `face_isPullback` and `face` supply their unique Cartesian faces. Proof irrelevance supplies higher coherence of the equalities in the scheme category. |
| Specified finite and integral coefficient identifications | `d.finiteRingIso u n` and `d.integralRingIso u`; `coefficientMap` uses their actual adjoint finite constant-section maps; `diagonalProjection` uses the same limit projections. |
| Actual ringed quotient sequence site Q_T | `quotientRing d T` is the published `SemilinearSections.systemRing` of the finite quotient sequence; `transition` is the actual quotient tower map. `modules` and `derived` are the published strict-system category and its ordinary derived category. |
| Coherent strict Weil isomorphism, not evaluated compatibility | `WeilDatum d sq K` extends the cube and contains `theta : pull d FX.hom ((reduction d X).obj K) ≅ (reduction d X).obj K`. `reduction` is exact diagonal followed by the universal K-flat derived scalar-extension pair for Delta A to Q. |
| Total diagram-site pullback, direct image and derived adjunction | `modulePush` is actual `SheafOfModules.pushforward` for `siteMap` and `coefficientMap`; `modulePull` is its universal left adjoint, i.e. the ordinary module pullback. Exactness allows `pull := modulePull.mapDerivedCategory`; `push := modulePush.rightDerivedFunctor`; `adjunction` is the canonical derived ordinary adjunction. |
| Canonical kappa, beta at all three coefficient presentations | `modulePushComp_exists` fixes direct-image composition on sections. `modulePullComp` is its adjunction conjugate and `pullComp` its exact localization. `kappa` pastes the two composition maps with the commutation equality; `beta` is literally `mateEquiv ... kappa.inv`. `integralKappa`, `integralBeta`, `finiteKappa`, `finiteBeta` use the published general ringed comparison/exchange and the canonical coefficient coherence of `d`. |
| Strict theta_E, Theta_B, Theta_D | `thetaE`, `thetaB`, `thetaD` are precisely the three displayed ordered composites, using diagram-site kappa/beta and the one `F.theta`. |
| P_n-linear evaluations and finite input structure | `evaluation` is the published exact semilinear evaluation; `moduleEvaluationPush_exists` fixes its ordinary comparison on component carriers; `moduleEvaluationPull_exists` fixes its tensor-unit mate. `evaluationPush_exists` retains the universal right-derived cochain-unit equation; `evaluationPull` is exact localization. `evaluationReduction_exists` retains the universal K-flat scalar counit. `finiteWeil` evaluates the strict input isomorphism through those identifications. |
| Evaluated B,D structures equal the finite blueprint formulas | `finiteThetaB` and `finiteThetaD` are evaluated diagram morphisms transported by `finiteBComparison` and `finiteDComparison`; `finiteThetaE` gives the finite formula for E; `finite_formulas` states both displayed finite composite equations, using `finiteWeil`, `finiteKappa`, `finiteBeta`. |
| Restrict Delta A to Q and transport to actual ambient B,D | `moduleRestriction_exists` fixes each finite scalar restriction and every original section/transition map, not just level objects. Its exact localization is `restriction`. `moduleRestrictionPull_exists` retains the module unit equation; `restrictionPush_exists` retains the common direct-image derived-unit equation for the two factorizations. `reductionRestriction_exists` fixes the strict reduction comparison by its K-flat counit. `cornerBComparison` and `cornerDComparison` compose precisely these identifications. `transport` applies restriction and conjugates by them. |
| Ambient Theta_A and Theta_C | `towerTheta 0` is `Phi(H.hom) ≫ transportedThetaB ≫ H.inv`; index 2 is the identical formula with H' and D. Indices 1,3 are the transported B,D structures. Dependent matching on Fin 4 retains the different corner objects. |
| Finite Theta_A and Theta_C | `finiteTheta ... n 0` uses the published h, and index 2 uses h'; the other two cases use evaluated B,D directly. No quotient-diagram lift of H or H' is introduced. |
| Restricted evaluations agree with ambient ones | `moduleRestrictionEvaluation_exists` is identity on original sections; `restrictionEvaluation` is its exact localization. `ambientPullEvaluation` is the termwise identity and `finiteRestrictionPull` is the published restricted coefficient pullback comparison. `ambientCornerComparison` fixes the four corner identifications; `towerTheta_evaluation` states the exact commuting equation for every corner and positive level. The underlying direct-image comparisons retain common universal units. |
| Canonical j from inverse automorphism, total Rlim | `modulePullLimit_exists` fixes its ordinary hom as `limit.post`. `pullLimit_exists` retains the common right-derived cochain-unit equation after identifying inverse-automorphism direct image with exact Frobenius pullback. `pullLimit` selects that unique normalized comparison. It is a natural isomorphism of total derived functors, not a map between independently selected triangles. |
| Theta_Z,infinity | `limitTheta i := pullLimit.hom.app _ ≫ completedRlim.map (towerTheta i)` for all four corners. |
| Precisely s_A, s and d | `sourceIdentification` is the defining reflexive identification S = Rlim A; `sourceBIdentification` is that identification followed by `Rlim.mapIso H`, giving s=Rlim(H)s_A. `targetIdentification` is the published `d.directImageRlimIso f'` at the prescribed strict pulled reduction tower, with direction T to Rlim D. |
| Theta_S and Theta_T | `sourceTheta` and `targetTheta` conjugate the exact limit structures by the preceding specified identifications, in the displayed order. |
| P_n-linear tensor reductions, including Frobenius chi | `sourceReducedTheta` and `targetReducedTheta` first use `(d.chi F.FY'.hom n).hom.app _` and then `d.reduction.map` of the completed structure. |
| All Theta sources are Frobenius pullbacks of targets | Explicit result types of all the individual definitions and every field of `CornerStructures d F`. The main constructor fills all fields with the above formulas. |

### Dependency declarations

- `def-weil-pbc-completed-base-change-map`: `Sheaf.Paper.CompletedBaseChangeMap`, `AlgebraicGeometry.Scheme.AdicCoefficientDatum.completedBaseChangeMap`.
- `def-weil-pbc-four-corners`: `Sheaf.Paper.FourCorners`, `AlgebraicGeometry.Scheme.AdicCoefficientDatum.fourCorners`.
- `def-weil-pbc-four-arrows`: `Sheaf.Paper.FourArrows`, `AlgebraicGeometry.Scheme.AdicCoefficientDatum.fourArrows`.
- `lem-weil-pbc-strict-tower-exchange-mate-normalization`: `Sheaf.Paper.StrictTowerExchangeMateNormalization`, `AlgebraicGeometry.Scheme.strictTowerExchangeMateNormalization`.
- `lem-weil-pbc-profinite-coefficient-inverse-image`: `Sheaf.AlgebraicGeometry.ProfiniteCoefficientInverseImage`, `AlgebraicGeometry.Scheme.proEtale_profinite_coefficient_inverse_image`.
- `lem-weil-pbc-diagram-site-realization`: `Sheaf.CategoryTheory.DiagramSiteRealization`, `CategoryTheory.exists_diagramSite_realization`.
- `lem-weil-pbc-proetale-derived-pullback-composition`: `Sheaf.Paper.IntegralFinitePullbackComposition`, `WeilConjectures.integralTowerGeneralPullbackComposition`.
- `def-weil-pbc-ambient-ringed-exchange`: `Sheaf.Paper.PbcActualRingedExchange`, `AlgebraicGeometry.Scheme.pbcActualCompletedAmbientExchange`.
- `lem-weil-ringed-tower-pushforward-limit-comparison`: `Sheaf.CategoryTheory.RingedTowerPushforwardLimitComparison`, `CategoryTheory.ringedTowerPushforwardLimitComparison`.
- `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`: `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`, `SheafOfModules.CanonicalTensorPullbackOfUniverses.ringedTopoiCanonicalDerivedTensorPullback`.
- `lem-weil-pbc-ringed-topoi-derived-pullback`: `Sheaf.Paper.RingedTopoiDerivedPullback`, `SheafOfModules.ringedTopoiDerivedPullback`.
- `lem-weil-pbc-ringed-topoi-derived-pushforward-composition`: `Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition`, `CategoryTheory.ringedToposDerivedPushforwardComposition`.
- `lem-weil-pbc-ringed-topoi-module-adjunction`: `Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction`, `SheafOfModules.module_pullback_pushforward_adjunction`.
- `lem-pc-derived-adjoint-functors`: `Sheaf.CategoryTheory.DerivedCategory.AdjointFunctors`, `CategoryTheory.Adjunction.exists_derived_adjunction_of_essentially_constant`.
- `def-weil-pbc-adjunction-mate`: existing Mathlib match `{'declaration': 'CategoryTheory.mateEquiv', 'file': 'Mathlib/CategoryTheory/Adjunction/Mates.lean', 'how': 'exact: with C, D, E, F, adj₁ : L₁ ⊣ R₁, adj₂ : L₂ ⊣ R₂, G, H as above, a TwoSquare G L₁ L₂ H is a transformation G ⋙ L₂ ⟶ L₁ ⋙ H (i.e. L₂G → HL₁) and `mateEquiv adj₁ adj₂ α : TwoSquare R₁ H G R₂` is R₁ ⋙ G ⟶ H ⋙ R₂ (i.e. GR₁ → R₂H), with the components of the statement (mateEquiv_apply / unit_mateEquiv, mateEquiv_counit); adjunctions, units and counits are CategoryTheory.Adjunction, .unit, .counit'}`.
- `prop-weil-pbc-rlim-functoriality`: `Sheaf.Paper.CompletedRlimFunctor`, `AlgebraicGeometry.Scheme.completedRlim_computation`.
- `def-weil-pbc-adic-coefficient-datum`: `Sheaf.Paper.AdicCoefficientDatum`, `AlgebraicGeometry.Scheme.completedReductionTower`.
- `def-pc-sheaf-restrict-scalars`: `Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`, `SheafOfModules.restrictScalars`.
- `prop-weil-pbc-direct-image-limits`: `Sheaf.Paper.CompletedDirectImageLimits`, `AlgebraicGeometry.Scheme.AdicCoefficientDatum.directImageRlimIso`.
- `lem-coef-semilinear-derived-sections`: `Sheaf.Paper.SemilinearDerivedSections`, `WeilConjectures.SemilinearSections.semilinearDerivedSections`.

The general arbitrary-compatible-ring-square comparison and exchange are retained by public
imports of their recorded composition/exchange modules; the completed-specialization primary
names are not substituted for these finite or uncompleted operations. `SheafOfModules.restrictScalars`
is used through the published `reductionRestrict` interface. The scalar-extension universal-pair
model is the already published `SheafOfModules.DerivedChangeOfRingsCochainModel` imported by the
semilinear dependency. No private scalar-extension or derived-category definition is supplied.
All dependency modules remain imported as required by the statement/proof plan.

### Edge cases and size check

- Identity Frobenius: the commutations and Cartesian faces exist; the pullback and mate
  normalizations recover the ordinary unit-normalized identity comparisons, rather than a
  free sign choice. The formulas are conjugation of the supplied strict identity structure.
- K=0: the strict reduction, all four corners and all induced structures are zero; no
  nonzero object or nonempty scheme is assumed.
- I=0: finite coefficients are A at every positive level. The transition and coefficient
  projection constructions still make sense and no inverse of I is used.
- Unit ideal / zero quotient rings: the constructions allow zero modules and zero rings;
  there is no nontriviality hypothesis added to finite coefficients.
- n=0 means the paper's first quotient A/I, never the exponent-zero quotient A/I^0.
- Arbitrary scheme universe t is retained: the small pro-etale site has object universe
  t+1 and morphism universe t; coefficients live in t+1 and the ordinary derived categories
  in t+2. No site-size equality is imposed. Explicit coefficient-universe instances and
  explicit vertical-slice equality transports prevent Lean's universe search from guessing
  a larger unresolved coefficient universe.
- Equality of derived maps is never inferred from their finite evaluations. The input
  and the B,D structures are actual strict derived morphisms before evaluation or Rlim.

### Searches for an existing definition

- `msearch.py ... leanfinder "Frobenius structures on quotient coefficient strict towers transported to derived inverse limits"`:
  8 hits concerning ring Frobenius / Witt vectors; none defines this strict quotient construction.
- `msearch.py ... leansearch "Frobenius action on completed derived inverse limits of quotient coefficient sheaf towers"`:
  8 Perfection/WittVector hits; no categorical corner structures.
- `msearch.py ... loogle "CategoryTheory.mateEquiv, CategoryTheory.Functor"`:
  12 abstract mate identities; the existing `mateEquiv` is used, but none defines these corners.
- `msearch.py ... grep "Frobenius.*tower|tower.*Frobenius|completed.*[Ff]robenius"`:
  no Mathlib match.
- `rg` in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for those Frobenius/tower
  combinations, and for the exact node id: no matching construction.
- `rg` in `/home/ubuntu/weil-newtargets-shared/lean/Sheaf`:
  `ZlFrobeniusCompactSupportComparison.lean` is a compact-support l-adic specialization,
  not this quotient-ring sequence-site/completed-base-change notion. The existing dependencies
  above give the required components and are reused.

No STATEMENT-DISPUTED finding, statement correction, new node, or dependency rebinding is required.

## Second reading by NF

I reopened the node and the complete module and checked every row of the clause mapping above.
This is a self-check: the dispatcher explicitly forbids starting other agents, and the independent
maintainer review remains the next independent reading. I do not claim a second worker was run.

The review caught and repaired three implementation mismatches: finite structures must be
P_n-linear evaluations of one coherent strict input (now `finiteWeil`, `finiteThetaB/D` and
`finite_formulas`); A and C must be conjugated only after ambient restriction (now the
separate `towerTheta` and `finiteTheta` definitions); and the completed source comparison
must be s_A rather than the comparison to B (now separate `sourceIdentification` and
`sourceBIdentification`). The final source and target reductions use chi for Frobenius itself.

I checked the order and direction of kappa, beta, all four conjugations, j, s_A and d against
the displayed node formulas. I checked that the finite and ambient categories keep their
coefficient actions, that the witnesses are precisely the existing `FiniteEtaleOriginWitness`
family, that all universal-comparison choices retain normalization equations, and that no
arbitrary map or mere Nonempty natural isomorphism substitutes for a canonical comparison.

### Validation

Only the authorized `scompile.py` file wrapper is used. Core probes checked the section
coefficient constructions, module adjunction and mate. The full file compiled cleanly as both sandbox and final library module (40.3 s and
40.7 s, respectively), with no errors or warnings. Delivery preflight results follow.

The prescribed `deliver2.py ... --no-push` completed successfully: dry-run commit
`725da6f514` passed the maintainer preflight and compilation; nothing was pushed by that run.
