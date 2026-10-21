/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N6
-/
module

public import Sheaf.Paper.CompletedRingStrictFiniteExchange
public import Sheaf.Paper.CompletedOpenExchangeTransport
public import Sheaf.Paper.CompleteProetaleStrictTowerRealization
public import Sheaf.CategoryTheory.LocalizedModuleExactForSystems
public import Sheaf.Paper.IntrinsicCompletionCompleted
public import Sheaf.Paper.ConstantCompletionEquivalence
public import Sheaf.AlgebraicGeometry.StrictConstantTowerOperations
public import Sheaf.AlgebraicGeometry.StrictTowerOpenExtension
public import Sheaf.AlgebraicGeometry.StrictTowerProperOpenCalculus
public import Sheaf.AlgebraicGeometry.FiniteOpenExchangeScalars
public import Sheaf.Paper.ExactProductFunctorStrictLimit
public import Sheaf.Paper.PbcQbarCompletedPullback

/-!
# The actual completed open exchange and its strict constant-coefficient mate

Source: Stacks Project, Tag 03DI, explicit extension-by-zero unit transpose;
blueprint main-20261015, sec-six-functors-basics/sk-prop-sf-cbc,
lem-cbc-completed-extension-zero-comparison.proof.md, finite exchange and final limit.
(blueprint: lem-cbc-completed-open-strict-mate-identification).

The endpoint comparisons reuse the published scalar, strict quotient, and normalized
inverse-limit comparisons. The actual strict exchange is constructed before evaluation.
The endpoint constructions and their naturality properties from
CompleteProetaleStrictTowerRealization are used; its compact-support realization theorem
is not used in this module.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

variable {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
variable {U' U T' T : Scheme.{u}} {v : U' ⟶ U} {j' : U' ⟶ T'}
  {j : U ⟶ T} {g : T' ⟶ T} [IsOpenImmersion j] [IsOpenImmersion j']
  (sq : OpenImmersionSquare v j' j g)

/-- The actual source Q, using reduction of j!K before strict derived pullback.
Source: blueprint finite open exchange
(blueprint: lem-cbc-completed-open-strict-mate-identification). -/
abbrev cbcOpenMateSource :=
  cbcDerivedOpenShriek d j inferInstance ⋙ completedReductionTower T d ⋙
    completedTowerPullback g d

/-- The actual target Q', with strict pullback preceding strict open extension.
Source: blueprint finite open exchange
(blueprint: lem-cbc-completed-open-strict-mate-identification). -/
abbrev cbcOpenMateTarget :=
  completedReductionTower U d ⋙ completedTowerPullback v d ⋙
    cbcStrictOpen d j' inferInstance

/-- The specified actual strict exchange, transported by the canonical quotient/open
comparison. Both constituent isomorphisms are already defined before evaluation.
Source: Stacks 03DI and blueprint finite exchange
(blueprint: lem-cbc-completed-open-strict-mate-identification). -/
def cbcOpenMateOmega (K : d.derived U) :
    (cbcOpenMateSource d (j := j) (g := g)).obj K ≅
      (cbcOpenMateTarget d (j' := j') (v := v)).obj K :=
  (completedTowerPullback g d).mapIso (cbcRealizationReduction d j K) ≪≫
    (cbcReductionStrictExchange d sq).app K

/-- M is the scalar restriction of the entire strict reduction tower of K.
Source: Stacks 099M and blueprint finite reductions
(blueprint: lem-cbc-completed-open-strict-mate-identification). -/
abbrev cbcOpenMateM := completedReductionTower U d ⋙ exchangeTowerRes d U

/-- N = G_g J_j M, in the derived category of constant-A strict towers.
Source: blueprint strict open exchange
(blueprint: lem-cbc-completed-open-strict-mate-identification). -/
abbrev cbcOpenMateN :=
  cbcOpenMateM d (U := U) ⋙ ProEtale.StrictTower.J A j ⋙ ProEtale.StrictTower.G A g

/-- N' = J_j' G_v M, with the same strict constant-coefficient operations.
Source: blueprint strict open exchange
(blueprint: lem-cbc-completed-open-strict-mate-identification). -/
abbrev cbcOpenMateN' :=
  cbcOpenMateM d (U := U) ⋙ ProEtale.StrictTower.G A v ⋙ ProEtale.StrictTower.J A j'

/-- The canonical source comparison a: r(Q) is identified with G_g J_j M.
It uses the normalized actual-to-datum pullback comparison, the scalar/pullback
comparison, and the quotient/open comparison, in that order.
Source: Stacks 03DI, 099N and blueprint scalar comparisons
(blueprint: lem-cbc-completed-open-strict-mate-identification). -/
def cbcOpenMateA (K : d.derived U) :
    (exchangeTowerRes d T').obj ((cbcOpenMateSource d (j := j) (g := g)).obj K) ≅
      (cbcOpenMateN d (j := j) (g := g)).obj K :=
  (exchangeTowerRes d T').mapIso
      ((cbcDatumTowerTransport d g).app
        ((completedReductionTower T d).obj
          ((cbcDerivedOpenShriek d j inferInstance).obj K))) ≪≫
    (exchangeResPull d g).app _ ≪≫
    (ProEtale.StrictTower.G A g).mapIso (cbcRealizationQuotientOpen d j K)

/-- The canonical target comparison b: r(Q') is identified with J_j' G_v M.
It first transports strict pullback, then commutes scalar restriction with open
extension, and finally uses the scalar/pullback comparison inside J_j'.
Source: Stacks 03DI, 099N and blueprint scalar comparisons
(blueprint: lem-cbc-completed-open-strict-mate-identification). -/
def cbcOpenMateB (K : d.derived U) :
    (exchangeTowerRes d T').obj ((cbcOpenMateTarget d (j' := j') (v := v)).obj K) ≅
      (cbcOpenMateN' d (j' := j') (v := v)).obj K :=
  (exchangeTowerRes d T').mapIso
      ((cbcStrictOpen d j' inferInstance).mapIso
        ((cbcDatumTowerTransport d v).app ((completedReductionTower U d).obj K))) ≪≫
    (cbcRealizationTowerScalarOpen d j').app _ ≪≫
    (ProEtale.StrictTower.J A j').mapIso
      ((exchangeResPull d v).app ((completedReductionTower U d).obj K))

/-- The already specified constant-A strict open unit-mate, at M = r(K_bullet).
Source: Stacks 03DI, normalized strict open calculus
(blueprint: lem-cbc-completed-open-strict-mate-identification). -/
def cbcOpenMateBeta (K : d.derived U) :
    (cbcOpenMateN d (j := j) (g := g)).obj K ≅
      (cbcOpenMateN' d (j' := j') (v := v)).obj K :=
  (ProEtale.StrictTower.beta A v j' j g sq.w
    (IsPullback.of_iso_pullback sq.toCommSq sq.isoPullback sq.hom_fst sq.hom_snd)).app
      ((cbcOpenMateM d (U := U)).obj K)

/-- Quasi-compactness of the base-changed open, supplied by the cartesian square.
Source: Stacks 01K5
(blueprint: lem-cbc-completed-open-strict-mate-identification). -/
abbrev cbcOpenMateQC [QuasiCompact j] : QuasiCompact j' :=
  MorphismProperty.of_isPullback
    (IsPullback.of_iso_pullback sq.toCommSq sq.isoPullback sq.hom_fst sq.hom_snd)
    (inferInstance : QuasiCompact j)

/-- The completed source endpoint, including the specified scalar/limit comparison
and strict quotient/open identification. No endpoint isomorphism is freely chosen.
Source: Stacks 099M, 099N and blueprint ordered limit
(blueprint: lem-cbc-completed-open-strict-mate-identification). -/
def cbcOpenMateCompletedA (K : d.derived U) :
    (cbcRealizationRes d T').mapDerivedCategory.obj
        ((d.completedPull g).obj ((cbcDerivedOpenShriek d j inferInstance).obj K)) ≅
      (completedRlim T' (exchangeConstantRing T' A)).obj
        ((cbcOpenMateN d (j := j) (g := g)).obj K) :=
  cbcRealizationPullLimit d g ((cbcDerivedOpenShriek d j inferInstance).obj K) ≪≫
    (completedRlim T' (exchangeConstantRing T' A)).mapIso
      ((ProEtale.StrictTower.G A g).mapIso (cbcRealizationQuotientOpen d j K))

/-- The completed target endpoint, before applying the normalized constant-A
open/limit comparison. The coefficient and pullback comparisons retain their units.
Source: Stacks 03DI, 099N and blueprint ordered limit
(blueprint: lem-cbc-completed-open-strict-mate-identification). -/
def cbcOpenMateCompletedB (K : d.derived U) :
    (cbcRealizationRes d T').mapDerivedCategory.obj
        ((cbcDerivedOpenShriek d j' inferInstance).obj ((d.completedPull v).obj K)) ≅
      (ProEtale.StrictTower.moduleJ A j').mapDerivedCategory.obj
        ((completedRlim U' (exchangeConstantRing U' A)).obj
          ((ProEtale.StrictTower.G A v).obj ((cbcOpenMateM d (U := U)).obj K))) :=
  (cbcRealizationDerivedScalarOpen d j').app ((d.completedPull v).obj K) ≪≫
    (ProEtale.StrictTower.moduleJ A j').mapDerivedCategory.mapIso
      (cbcRealizationPullLimit d v K)

/-- The actual finite strict exchange restricts to the constant-A open-unit mate,
and the canonical completed exchange is its ordered derived inverse limit.
The first equality lies in the derived category of strict towers, before evaluation.
The second equality writes both specified endpoint identifications explicitly.

Source: Stacks Tag 03DI, explicit transpose; blueprint main-20261015,
lem-cbc-completed-extension-zero-comparison.proof.md, finite and final-limit paragraphs
(blueprint: lem-cbc-completed-open-strict-mate-identification).
Proof:
1. Apply completedRingStrictFiniteExchange to the actual strict exchange and
transport its source by cbcRealizationReduction. This retains its inverse's open
unit normalization, completed scalar linearity, and every quotient transition.
2. ConstantCompletionEquivalence identifies the finite reductions and strict
quotient units. Restriction leaves the direct-sum extension presheaf unchanged;
its unit and counit are the same extension sections, by OpenTensorNormalization.
The source and target comparisons are exactly cbcOpenMateA and cbcOpenMateB.
3. Transpose the inverse exchange under the open adjunction. Its pulled-back unit
and square compositor are those of StrictTower.betaInvApp. FiniteOpenExchangeScalars
identifies the scalar actions and transitions. The two inverse strict maps agree.
4. Localize that equality at tower quasi-isomorphisms and invert it. This yields
the first displayed equality without any faithfulness assumption on evaluation.
5. The cartesian square makes j' quasi-compact. Ringed open extension is exact and
preserves products; pro-etale countable products are exact. Apply
exactProductFunctorStrictLimit to obtain precisely cbcRealizationOpenLimit.
6. The scalar/limit and scalar/open comparisons identify the completed endpoints,
including their quotient completion units. Ringed open scalar/limit coherence
identifies the two orders of taking these normalized comparisons.
7. The completed comparison first takes Rlim of the actual strict exchange and
then applies the inverse open/limit comparison. Functoriality of Rlim and step 4
therefore give the second displayed equality, in that order.
8. Every constituent is natural in K. Evaluation of the already specified strict
map is the finite open exchange by completedRingStrictFiniteExchange; the last
clause records its finite source transport explicitly. No origins or degree bound
are used at any step. -/
theorem completedOpenStrictMateIdentification [QuasiCompact j]
    (r : ℕ) (a : Fin r → A) (ha : Ideal.span (Set.range a) = d.ideal)
    (K : (cbcCompleteProperty d U r a ha).FullSubcategory)
    (_completeOpen : cbcCompleteProperty d T r a ha
      ((cbcDerivedOpenShriek d j inferInstance).obj K.obj)) :
    (exchangeTowerRes d T').map (cbcOpenMateOmega d sq K.obj).hom ≫
        (cbcOpenMateB d (j' := j') (v := v) K.obj).hom =
      (cbcOpenMateA d (j := j) (g := g) K.obj).hom ≫
        (cbcOpenMateBeta d sq K.obj).hom ∧
    (cbcRealizationRes d T').mapDerivedCategory.map
        ((cbcDatumCompletedExchange d sq r a ha).app K) ≫
          (cbcOpenMateCompletedB d (j' := j') (v := v) K.obj).hom =
      (cbcOpenMateCompletedA d (j := j) (g := g) K.obj).hom ≫
        (completedRlim T' (exchangeConstantRing T' A)).map
          (cbcOpenMateBeta d sq K.obj).hom ≫
        (@cbcRealizationOpenLimit _ _ d U' T' j' inferInstance
          (cbcOpenMateQC sq)).inv.app
            ((ProEtale.StrictTower.G A v).obj ((cbcOpenMateM d (U := U)).obj K.obj)) ∧
    ∀ n : ℕ,
      HEq
        ((pbcTowerEvaluation T' (pbcAdicCompletion T' d) n).map
            (cbcOpenMateOmega d sq K.obj).hom ≫
          (cbcTargetFiniteComparison d sq n).hom.app K.obj)
        ((pbcTowerEvaluation T' (pbcAdicCompletion T' d) n).map
            ((completedTowerPullback g d).map (cbcRealizationReduction d j K.obj).hom) ≫
          (cbcSourceFiniteComparison d sq n).hom.app K.obj ≫
          (cbcFiniteExchange d sq n).hom.app ((cbcFiniteReduction d U n).obj K.obj)) := by
  sorry

private def reductionOpenNatIso :
    completedReductionTower U d ⋙ cbcRealizationJ d j ≅
      cbcDerivedOpenShriek d j inferInstance ⋙ completedReductionTower T d :=
  NatIso.ofComponents (fun K ↦ (cbcRealizationReduction d j K).symm)
    (fun f ↦ (cbcRealizationReductionInv_properties d j).2 _ _ f)

private def quotientOpenNatIso :
    cbcDerivedOpenShriek d j inferInstance ⋙ completedReductionTower T d ⋙
        exchangeTowerRes d T ≅
      cbcOpenMateM d (U := U) ⋙ ProEtale.StrictTower.J A j :=
  Functor.isoWhiskerRight (reductionOpenNatIso d (j := j)).symm (exchangeTowerRes d T) ≪≫
    Functor.isoWhiskerLeft (completedReductionTower U d) (cbcRealizationTowerScalarOpen d j)

private def pullLimitNatIso {S V : Scheme.{u}} (f : S ⟶ V) :
    d.completedPull f ⋙ (cbcRealizationRes d S).mapDerivedCategory ≅
      completedReductionTower V d ⋙ exchangeTowerRes d V ⋙
        ProEtale.StrictTower.G A f ⋙ completedRlim S (exchangeConstantRing S A) :=
  Functor.isoWhiskerLeft (completedReductionTower V d ⋙ d.towerPull f)
      (cbcRealizationResLimit d S) ≪≫
    Functor.isoWhiskerLeft (completedReductionTower V d)
      (Functor.isoWhiskerRight (exchangeResPull d f)
        (completedRlim S (exchangeConstantRing S A)))

private def omegaNatIso :
    cbcOpenMateSource d (j := j) (g := g) ≅
      cbcOpenMateTarget d (j' := j') (v := v) :=
  Functor.isoWhiskerRight (reductionOpenNatIso d (j := j)).symm
      (completedTowerPullback g d) ≪≫ cbcReductionStrictExchange d sq

private def sourceNatIso :
    cbcOpenMateSource d (j := j) (g := g) ⋙ exchangeTowerRes d T' ≅
      cbcOpenMateN d (j := j) (g := g) :=
  Functor.isoWhiskerLeft (cbcDerivedOpenShriek d j inferInstance ⋙ completedReductionTower T d)
      (Functor.isoWhiskerRight (cbcDatumTowerTransport d g) (exchangeTowerRes d T')) ≪≫
    Functor.isoWhiskerLeft
      (cbcDerivedOpenShriek d j inferInstance ⋙ completedReductionTower T d)
      (exchangeResPull d g) ≪≫
    Functor.isoWhiskerRight (quotientOpenNatIso d (j := j)) (ProEtale.StrictTower.G A g)

private def targetNatIso :
    cbcOpenMateTarget d (j' := j') (v := v) ⋙ exchangeTowerRes d T' ≅
      cbcOpenMateN' d (j' := j') (v := v) :=
  Functor.isoWhiskerLeft (completedReductionTower U d)
      (Functor.isoWhiskerRight
        (Functor.isoWhiskerRight (cbcDatumTowerTransport d v)
        (cbcStrictOpen d j' inferInstance)) (exchangeTowerRes d T')) ≪≫
    Functor.isoWhiskerLeft (completedReductionTower U d ⋙ d.towerPull v)
      (cbcRealizationTowerScalarOpen d j') ≪≫
    Functor.isoWhiskerLeft (completedReductionTower U d)
      (Functor.isoWhiskerRight (exchangeResPull d v) (ProEtale.StrictTower.J A j'))

private def completedSourceNatIso :
    cbcDerivedOpenShriek d j inferInstance ⋙ d.completedPull g ⋙
        (cbcRealizationRes d T').mapDerivedCategory ≅
      cbcOpenMateN d (j := j) (g := g) ⋙
        completedRlim T' (exchangeConstantRing T' A) :=
  Functor.isoWhiskerLeft (cbcDerivedOpenShriek d j inferInstance) (pullLimitNatIso d g) ≪≫
    Functor.isoWhiskerRight (quotientOpenNatIso d (j := j))
      (ProEtale.StrictTower.G A g ⋙ completedRlim T' (exchangeConstantRing T' A))

private def completedTargetNatIso :
    d.completedPull v ⋙ cbcDerivedOpenShriek d j' inferInstance ⋙
        (cbcRealizationRes d T').mapDerivedCategory ≅
      cbcOpenMateM d (U := U) ⋙ ProEtale.StrictTower.G A v ⋙
        completedRlim U' (exchangeConstantRing U' A) ⋙
          (ProEtale.StrictTower.moduleJ A j').mapDerivedCategory :=
  Functor.isoWhiskerLeft (d.completedPull v) (cbcRealizationDerivedScalarOpen d j') ≪≫
    Functor.isoWhiskerRight (pullLimitNatIso d v)
      (ProEtale.StrictTower.moduleJ A j').mapDerivedCategory

/-- Naturality of the specified actual strict exchange and its strict and completed
endpoint comparisons, on the full category of the complete inputs in the statement.
Source: Stacks 03DI, natural Hom adjunction, and blueprint ordered limit
(blueprint: lem-cbc-completed-open-strict-mate-identification).
Proof: the quotient/open comparison is natural by its open-unit transpose formula.
The actual strict exchange is a natural isomorphism before restriction or evaluation.
Scalar restriction, derived pullback and Rlim are functors. Each endpoint comparison
is a composite of their published natural comparisons. Apply their naturality
identities and functoriality of composition to obtain each displayed square. This
is the naturality argument of Step 8 of the node, and uses no evaluation criterion. -/
theorem completedOpenStrictMateIdentification_naturality [QuasiCompact j]
    (r : ℕ) (a : Fin r → A) (ha : Ideal.span (Set.range a) = d.ideal)
    (K L : (cbcCompleteProperty d U r a ha).FullSubcategory) (f : K ⟶ L)
    (_completeOpenK : cbcCompleteProperty d T r a ha
      ((cbcDerivedOpenShriek d j inferInstance).obj K.obj))
    (_completeOpenL : cbcCompleteProperty d T r a ha
      ((cbcDerivedOpenShriek d j inferInstance).obj L.obj)) :
    (cbcOpenMateSource d (j := j) (g := g)).map f.hom ≫
        (cbcOpenMateOmega d sq L.obj).hom =
      (cbcOpenMateOmega d sq K.obj).hom ≫
        (cbcOpenMateTarget d (j' := j') (v := v)).map f.hom ∧
    (exchangeTowerRes d T').map
        ((cbcOpenMateSource d (j := j) (g := g)).map f.hom) ≫
          (cbcOpenMateA d (j := j) (g := g) L.obj).hom =
      (cbcOpenMateA d (j := j) (g := g) K.obj).hom ≫
        (cbcOpenMateN d (j := j) (g := g)).map f.hom ∧
    (exchangeTowerRes d T').map
        ((cbcOpenMateTarget d (j' := j') (v := v)).map f.hom) ≫
          (cbcOpenMateB d (j' := j') (v := v) L.obj).hom =
      (cbcOpenMateB d (j' := j') (v := v) K.obj).hom ≫
        (cbcOpenMateN' d (j' := j') (v := v)).map f.hom ∧
    (cbcRealizationRes d T').mapDerivedCategory.map
        ((d.completedPull g).map ((cbcDerivedOpenShriek d j inferInstance).map f.hom)) ≫
          (cbcOpenMateCompletedA d (j := j) (g := g) L.obj).hom =
      (cbcOpenMateCompletedA d (j := j) (g := g) K.obj).hom ≫
        (completedRlim T' (exchangeConstantRing T' A)).map
          ((cbcOpenMateN d (j := j) (g := g)).map f.hom) ∧
    (cbcRealizationRes d T').mapDerivedCategory.map
        ((cbcDerivedOpenShriek d j' inferInstance).map ((d.completedPull v).map f.hom)) ≫
          (cbcOpenMateCompletedB d (j' := j') (v := v) L.obj).hom =
      (cbcOpenMateCompletedB d (j' := j') (v := v) K.obj).hom ≫
        (ProEtale.StrictTower.moduleJ A j').mapDerivedCategory.map
          ((completedRlim U' (exchangeConstantRing U' A)).map
            ((ProEtale.StrictTower.G A v).map ((cbcOpenMateM d (U := U)).map f.hom))) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact (omegaNatIso d sq).hom.naturality f.hom
  · exact (sourceNatIso d (j := j) (g := g)).hom.naturality f.hom
  · exact (targetNatIso d (j' := j') (v := v)).hom.naturality f.hom
  · exact (completedSourceNatIso d (j := j) (g := g)).hom.naturality f.hom
  · exact (completedTargetNatIso d (j' := j') (v := v)).hom.naturality f.hom

end AlgebraicGeometry.Scheme
