# AlgebraicGeometry.Scheme.derived_finite_quotient_coherence

## Reason

The only Lean use of this six-conjunct lemma is `(derived_finite_quotient_coherence
 g d).1 K a b h` in `adicPresentationFiniteIso_transition`. The consumer needs only
the canonical finite evaluation transition square. None of the other five conjuncts,
`cbcFiniteOrdinaryTarget`, or `cbcFiniteOrdinaryNormalization` has a Lean consumer.
The only DAG proof-dependency parent is the presentation-transport node, whose step
also uses only that square. The finite-interface node mentions this lemma only in
its historical metadata, not in its dependencies. The unit has empty realized statement
and step lists. This is a direct proof of the needed square and pruning of an unused
stronger intermediate result, under the worker brief §8d and stage 3 §2.

No retained theorem statement is weakened. The original mathematical node and its
proof plan remain, with its Lean attachment set to null. Its module is withdrawn via
`deleted.txt`; no declaration of WeilConjectures is removed or changed. The attempted
complete six-clause proof is preserved in the worker scratchpad, outside the delivery.

## Old

The withdrawn declarations, verbatim:

```lean
abbrev cbcFiniteOrdinaryTarget (n : ℕ) :=
  reductionChange Y (completedReductionProjection Y d n) ⋙
    completedReductionFiniteModules g d n

/-- The ordinary finite normalization is the adjunct of the actual quotient map.
Source: CBC finite-reduction compatibility, Step 9; Stacks 06YY
(blueprint: lem-cbc-derived-finite-quotient-coherence). -/
def cbcFiniteOrdinaryNormalization (a b : ℕ) (h : a ≤ b) :
    cbcFiniteOrdinaryTarget g d b ⋙ reductionChange X (reductionCoefficientMap X d b a h) ⟶
      cbcFiniteOrdinaryTarget g d a :=
  Functor.whiskerRight (completedReductionOrdinaryTransition g d a b h)
      (reductionChange X (reductionCoefficientMap X d b a h)) ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (cbcFiniteOrdinaryTarget g d a)
      (pbcScalarAdjunction (reductionCoefficientMap X d b a h)).counit ≫
    (cbcFiniteOrdinaryTarget g d a).rightUnitor.hom

/-- The canonical finite evaluation commutes with every strict quotient transition.
Its finite target normalizations have the prescribed balanced tensor formula, descend
through the canonical computation maps, and satisfy the unit and quotient cocycle.
Source: main-20261015, sk-prop-sf-cbc, completed extension-by-zero comparison proof,
finite-reduction compatibility (blueprint: lem-cbc-derived-finite-quotient-coherence).

Proof:
1. Put R=constant A, B=the completed coefficient sheaf, and S_n=the finite sheaf.
The constant-completion theorem gives flat R→B and the normalized common quotients.
Choose a flat-term K-flat B-model P of K and one objectwise flat-term K-flat strict
R-tower resolution V_n→S_n, using diagram K-flat replacements, not unrelated levels.
2. Form H_n=Tot(P tensor_R V_n). Balancing identifies this with tensor over B of P
and B tensor_R V_n. Change of rings and total tensor make H a resolving B-tower.
3. Flat scalar restriction makes P K-flat over R. Thus 1 tensor v_n is a
quasi-isomorphism. Common-quotient balancing gives a strict quasi-isomorphism
r:H→(P tensor_B S_n)_n, representing the canonical reduction tower.
4. The ordinary finite comparison beta_n identifies the pullback of P tensor_B S_n
with finite inverse image D_n. On sections its scalar is pi_n(b')c_n(s).
Finite constant-map naturality makes beta commute with every quotient.
5. Pullback/tensor coherence identifies beta_n G(r_n) with 1 tensor g_R^*v_n on
Tot(G(P) tensor_R' g_R^*V_n). The inverse balancing inserts the scalar 1.
6. Ringed pullback preserves K-flatness and flat terms. Flat scalar restriction
makes G(P) K-flat over R'. Exact constant inverse image preserves the acyclic
cone of v_n; tensoring it with G(P) is acyclic. Hence these maps are quasi-isomorphisms
and form one morphism of strict towers. No quotient is assumed K-flat over B.
7. The universal tower counit and inverse of L(r) give chi:L R(K)→Q'G(H).
Compose with Q'(beta G(r)). Evaluation normalization identifies its components with
the prescribed constant-completion comparisons, independently of both resolutions.
8. Since this is a map of derived strict towers, its evaluations commute with every
transition, giving the first equality with the canonical restriction composition.
9. Finite change of rings and exact finite inverse image preserve K-flat models.
Successive quotient extension is ordinary balancing: (x tensor r) tensor s maps to
x tensor q(r)s, with inverse inserting 1. The formula below uses scalar-first tensors.
The universal scalar counits give precisely its derived representative equation.
At equal indices it is the scalar unitor. For c≥b≥a both reassociations send a pure
triple tensor to x tensor q_ca(r_c)q_ba(r_b)r_a, giving the quotient cocycle. -/
theorem derived_finite_quotient_coherence :
    (∀ (K : DerivedCategory (pbcModules Y (pbcAdicCompletion Y d)))
      (a b : ℕ) (h : a ≤ b),
      (completedReductionFiniteEvaluation g d b).hom.app K ≫
          (pbcDerivedRestrict (completedReductionProjection X d b)).map
            ((completedReductionTargetTransition g d a b h).app K) ≫
          (pbcDerivedRestrictComp (completedReductionProjection X d b)
            (reductionCoefficientMap X d b a h) (completedReductionProjection X d a)
            (completedReductionProjection_comp X d b a h)).hom.app
              ((completedReductionFiniteTarget g d a).obj K) =
        (pbcTowerTransition X (pbcAdicCompletion X d) b a h).app
            ((completedTowerPullback g d).obj ((completedReductionTower Y d).obj K)) ≫
          (completedReductionFiniteEvaluation g d a).hom.app K) ∧
    (∀ (K : DerivedCategory (pbcModules Y (pbcAdicCompletion Y d)))
      (a b : ℕ) (h : a ≤ b), IsIso (completedReductionTargetNormalization g d K a b h)) ∧
    (∀ (a b : ℕ) (h : a ≤ b)
      (M : pbcModules Y (pbcAdicCompletion Y d)) (V : Y.ProEt) (U : X.ProEt)
      (f : U ⟶ (proEtaleBaseChange g).obj V)
      (s : (reductionCoefficient X d a).obj.obj (op U))
      (r : (reductionCoefficient X d b).obj.obj (op U))
      (z : (reductionCoefficient Y d b).obj.obj (op V)) (x : M.val.obj (op V)),
      ((cbcFiniteOrdinaryNormalization g d a b h).app M).val.app (op U)
          (pbcTensorSection (reductionCoefficientMap X d b a h)
            ((cbcFiniteOrdinaryTarget g d b).obj M) (op U) s
            (completedReductionFiniteGenerator g d b M V U f r z x)) =
        completedReductionFiniteGenerator g d a M V U f
          (((reductionCoefficientMap X d b a h).hom.app (op U) r) * s)
          ((reductionCoefficientMap Y d b a h).hom.app (op V) z) x) ∧
    (∀ (a b : ℕ) (h : a ≤ b)
      (P : CochainComplex (pbcModules Y (pbcAdicCompletion Y d)) ℤ),
      CochainComplex.IsKFlatIndependentCoefficients (R := pbcAdicCompletion Y d) P →
      (reductionDerivedChange X (reductionCoefficientMap X d b a h)).map
          (completedReductionFiniteModelMap g d b P) ≫
        pbcComplexCounit (reductionCoefficientMap X d b a h)
          (((cbcFiniteOrdinaryTarget g d b).mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
          (cbcFiniteOrdinaryNormalization g d a b h) (.up ℤ)).app P) =
      completedReductionTargetNormalization g d (DerivedCategory.Q.obj P) a b h ≫
        completedReductionFiniteModelMap g d a P) ∧
    (∀ (K : DerivedCategory (pbcModules Y (pbcAdicCompletion Y d)))
      (a b c : ℕ) (hab : a ≤ b) (hbc : b ≤ c),
      (reductionDerivedChange X (reductionCoefficientMap X d b a hab)).map
          (completedReductionTargetNormalization g d K b c hbc) ≫
        completedReductionTargetNormalization g d K a b hab =
      (completedReductionQuotientAssoc d X a b c hab hbc
          ((completedReductionFiniteTarget g d c).obj K)).hom ≫
        completedReductionTargetNormalization g d K a c (hab.trans hbc)) ∧
    ∀ (K : DerivedCategory (pbcModules Y (pbcAdicCompletion Y d))) (a : ℕ),
      completedReductionTargetNormalization g d K a a (le_refl a) =
        completedReductionUnit d X a ((completedReductionFiniteTarget g d a).obj K) := by
  sorry
```

The consumer privately imported `Sheaf.Paper.DerivedFiniteQuotientCoherence` and used
`have hc := (derived_finite_quotient_coherence g d).1 K a b h`.

## New

The former item module is withdrawn. The new direct theorem is fully proved:

```lean
theorem finite_quotient_transition_compatibility
    (K : DerivedCategory (pbcModules Y (pbcAdicCompletion Y d)))
    (a b : ℕ) (h : a ≤ b) :
    (completedReductionFiniteEvaluation g d b).hom.app K ≫
        (pbcDerivedRestrict (completedReductionProjection X d b)).map
          ((completedReductionTargetTransition g d a b h).app K) ≫
        (pbcDerivedRestrictComp (completedReductionProjection X d b)
          (reductionCoefficientMap X d b a h) (completedReductionProjection X d a)
          (completedReductionProjection_comp X d b a h)).hom.app
            ((completedReductionFiniteTarget g d a).obj K) =
      (pbcTowerTransition X (pbcAdicCompletion X d) b a h).app
          ((completedTowerPullback g d).obj ((completedReductionTower Y d).obj K)) ≫
        (completedReductionFiniteEvaluation g d a).hom.app K
```

The consumer privately imports `Sheaf.Paper.FiniteQuotientTransitionCompatibility` and
uses `have hc := finite_quotient_transition_compatibility g d K a b h`. These are its
only two changed lines. Its public imports, declaration signatures, definition bodies,
and remaining proofs are identical to the current source.

All coefficient, tensor, pullback, localization and canonical-map definitions are
unchanged. Every target has its existing statement and definitions; no target meaning
changes. The independent reader checks the shorter proof route and the withdrawal.
The new theorem quantifies over all K and all a≤b, including a=b and the first positive
quotient. Zero objects and zero morphisms need no special assumption: the proof uses
naturality and invertibility of the computation on a K-flat resolution.

## Users

`tools/downstream.py Sheaf.Paper.DerivedFiniteQuotientCoherence --uses
 derived_finite_quotient_coherence` lists 21 downstream modules and only one external
use of the declaration. The table records all of them and their current claim holders.
Only the unclaimed direct consumer is edited. All other consumers retain exactly the
same statements and definitions through that consumer's unchanged public interface.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.AdicPullbackPresentationTransport | unclaimed | Private import and one proof application changed; every statement and definition preserved. |
| Sheaf.Paper.CompactSupportProjectionFormula | unclaimed | Transitive proof dependency only; source and exported statements unchanged. |
| Sheaf.Paper.CompleteCompactSupportProetale | unclaimed | Transitive proof dependency only; source and exported statements unchanged. |
| Sheaf.Paper.CompleteProetaleStrictTowerRealization | unclaimed | Transitive proof dependency only; source and exported statements unchanged. |
| Sheaf.Paper.CompletedFiniteComparisonModels | unclaimed | Transitive proof dependency only; source and exported statements unchanged. |
| Sheaf.Paper.CompletedFiniteExchangeCoordinates | unclaimed | Transitive proof dependency only; source and exported statements unchanged. |
| Sheaf.Paper.CompletedOpenFiniteEtaleOrigins | unclaimed | Transitive proof dependency only; source and exported statements unchanged. |
| Sheaf.Paper.CompletedOpenStrictMateIdentification | unclaimed | Transitive proof dependency only; source and exported statements unchanged. |
| Sheaf.Paper.CompletedRingStrictFiniteExchange | M3 | Transitive proof dependency only; source and exported statements unchanged. |
| Sheaf.Paper.CompletedStrictOpenExchange | unclaimed | Transitive proof dependency only; source and exported statements unchanged. |
| Sheaf.Paper.ExtensionZeroPerfectModelTransport | unclaimed | Transitive proof dependency only; source and exported statements unchanged. |
| Sheaf.Paper.ExtensionZeroStratifiedPerfect | unclaimed | Transitive proof dependency only; source and exported statements unchanged. |
| Sheaf.Paper.NormalizedCoefficientFamilies | unclaimed | Transitive proof dependency only; source and exported statements unchanged. |
| Sheaf.Paper.NormalizedFiniteComparisonExistence | R4 | Transitive proof dependency only; source and exported statements unchanged. |
| Sheaf.Paper.RationalPullbackCompositionCoherence | unclaimed | Transitive proof dependency only; source and exported statements unchanged. |
| Sheaf.Paper.RationalRealizationPullbackComparison | unclaimed | Transitive proof dependency only; source and exported statements unchanged. |
| Sheaf.Paper.RationalRealizationScalarCoherence | G7 | Transitive proof dependency only; source and exported statements unchanged. |
| Sheaf.Paper.ZlFrameworkOpenExchange | unclaimed | Transitive proof dependency only; source and exported statements unchanged. |
| Sheaf.Paper.ZlFrobeniusCompactSupportComparison | unclaimed | Transitive proof dependency only; source and exported statements unchanged. |
| Sheaf.Paper.ZlShriekComposition | unclaimed | Transitive proof dependency only; source and exported statements unchanged. |
| Sheaf.SixFunctors.OpenExchangeRoosRestriction | unclaimed | Transitive proof dependency only; source and exported statements unchanged. |


The unit-route import flag concerns
`lem-weil-pbc-flat-common-quotient-reduction-tower`, realized in Step 1 of
`sk-lem-integral-models`. The original CBC node explicitly lists this node in
its maintainer-approved `tool_uses`, and its `split_report.tool_uses` calls it a
generic common-quotient comparison tool for a simultaneous tensor resolution.
SETUP.md's "Tool lemmas and the unit route" rule permits treating that use as
a tool use, independently of the integral-models unit's own proof. The new finite
square proof uses the published model normalizations instead of reconstructing
that resolution. No statement, step, dependency, or realization of
`sk-lem-integral-models` is changed. Its tool module and existing consumer
`Sheaf.Paper.RingedCommonQuotientPullbackComparison` remain verbatim. Thus removal
of this generic tool from the CBC subargument bypasses no unit step.

The original consumer was also compiled against an empty withdrawn item module.
It failed at line 1195 with `Unknown identifier derived_finite_quotient_coherence`
(and the consequent unsolved transition square), in 35.2 seconds. The adapted consumer
compiled in 38 seconds. Its two changed lines are thus necessary; no other edits occur.
The shared consumer claim is unclaimed. Report.md records this under Forced adaptations.

## Status

landed 20261022T023437-L-822290 2026-10-22 (merge of deliver/J4/Sheaf.Paper.DerivedFiniteQuotientCoherence)
