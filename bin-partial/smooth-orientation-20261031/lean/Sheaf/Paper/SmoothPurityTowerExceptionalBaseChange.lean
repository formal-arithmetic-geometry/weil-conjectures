/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U8
-/
module

public import Sheaf.Paper.ExceptionalBaseChangeIntegralMaps
import Sheaf.Paper.SmoothPurityTowerFiniteMateCriterion
import Sheaf.Paper.ExceptionalBaseChangeIntegralDataExistence

/-! # Exceptional base change for strict towers and integral coefficients

Source: latest blueprint, sk-prop-sp-purity-bc-tower, clauses (1)--(3)
(blueprint: det-sp-tower-exceptional-bc).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.Scheme WeilConjectures Opposite
namespace AlgebraicGeometry.ProEtale.SpExceptionalBaseChange
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
  (q : SpTowerCalculus.Coordinates l E b)
variable {X' X Y' Y : Scheme.{u}} {u' : X' ⟶ X} {f' : X' ⟶ Y'}
  {f : X ⟶ Y} {v : Y' ⟶ Y} {sq : IsPullback u' f' f v} {c : Compactification f}
  (a : SpTowerMate.Data l E b o q sq c)

private theorem isIso_app_of_iso {C D : Type*} [Category C] [Category D]
    {F G : C ⥤ D} (t : F ⟶ G) {M N : C} (e : M ≅ N)
    (hM : IsIso (t.app M)) : IsIso (t.app N) := by
  have := hM
  have : IsIso (F.map e.hom ≫ t.app N) := by
    rw [t.naturality]
    infer_instance
  exact IsIso.of_isIso_comp_left (F.map e.hom) (t.app N)

private theorem normalized_of_iso (T : Scheme.{u})
    (D : SpCoefficientTowersAbelian l E T) {M N : spDerivedCoefficientTowers l E T D}
    (e : M ≅ N) (hM : IsSpNormalizedTower l E T D M) :
    IsSpNormalizedTower l E T D N := by
  intro m n h
  exact isIso_app_of_iso (D.reduction h) e (hM m n h)

private theorem mate_isIso_of_finite (x : SpTowerShriek.OpenExchange l E b o)
    (hb : IsIso (SpTowerMate.beta l E b o q a x))
    (hfinite : ∀ (n : ℕ)
      (K : spFiniteConstructibleTorCategory Y (SpTowerShriek.R l E n)),
      IsIso ((SpTowerMate.finiteExchange l E b (sq := sq) (c := c) n).app
        ((a.levels.right n).obj K).obj))
    (hlaws : SpTowerMate.Laws l E b o q a x hb hfinite)
    (hm : ∀ (n : ℕ)
      (K : spFiniteConstructibleTorCategory Y (SpTowerShriek.R l E n)),
      IsIso (SpTowerMate.finiteMate l E b o q a n K (hfinite n K))) :
    IsIso (SpTowerMate.mate l E b o q a x hb) := by
  apply (NatTrans.isIso_iff_isIso_app _).2
  intro K
  let e := (SpTowerMate.mate l E b o q a x hb).app K
  have he (n : ℕ) :
      IsIso ((spDerivedCoefficientEvaluation l E X' (q.abelian X') n).map e.hom) := by
    have := hm n ((SpTowerGluing.level l E b q Y n).obj K)
    have : IsIso
        ((spDerivedCoefficientEvaluation l E X' (q.abelian X') n).map e.hom ≫
          (SpTowerMate.targetComparison l E b o q a n K).hom) := by
      rw [hlaws.evaluation]
      infer_instance
    exact IsIso.of_isIso_comp_right
      ((spDerivedCoefficientEvaluation l E X' (q.abelian X') n).map e.hom)
      (SpTowerMate.targetComparison l E b o q a n K).hom
  have : IsIso ((SpTowerCalculus.realization l E b X' (q.abelian X')).functor.map
      e.hom) := (b.calculus X').detects _ fun n ↦
    (NatIso.isIso_map_iff (SpTowerCalculus.levelComparison l E b q X' n) e.hom).mpr (he n)
  have : IsIso e.hom := isIso_of_reflects_iso _
    (SpTowerCalculus.realization l E b X' (q.abelian X')).functor
  have : IsIso ((SpTowerCalculus.inclusion l E b q X').map e) := by
    change IsIso e.hom
    infer_instance
  exact isIso_of_reflects_iso e (SpTowerCalculus.inclusion l E b q X')

private theorem counit_transport
    {C D C' D' A B A' B' : Type*}
    [Category C] [Category D] [Category C'] [Category D']
    [Category A] [Category B] [Category A'] [Category B']
    (rC : C ⥤ A) (rD : D ⥤ B) (rC' : C' ⥤ A') (rD' : D' ⥤ B')
    [rD'.Faithful]
    (F : C ⥤ D) (G : D ⥤ C) (F' : C' ⥤ D') (G' : D' ⥤ C')
    (U : C ⥤ C') (V : D ⥤ D')
    (Ft : A ⥤ B) (Gt : B ⥤ A) (Ft' : A' ⥤ B') (Gt' : B' ⥤ A')
    (Ut : A ⥤ A') (Vt : B ⥤ B')
    (ad : F ⊣ G) (ad' : F' ⊣ G') (adt : Ft ⊣ Gt) (adt' : Ft' ⊣ Gt')
    (sf : F ⋙ rD ≅ rC ⋙ Ft) (sf' : F' ⋙ rD' ≅ rC' ⋙ Ft')
    (sg : G ⋙ rC ≅ rD ⋙ Gt) (sg' : G' ⋙ rC' ≅ rD' ⋙ Gt')
    (su : U ⋙ rC' ≅ rC ⋙ Ut) (sv : V ⋙ rD' ≅ rD ⋙ Vt)
    (bt : Ft ⋙ Vt ⟶ Ut ⋙ Ft') (mt : Gt ⋙ Ut ⟶ Vt ⋙ Gt')
    (beta : F ⋙ V ≅ U ⋙ F') (K : D)
    (e : U.obj (G.obj K) ⟶ G'.obj (V.obj K))
    (hb : rD'.map (beta.hom.app (G.obj K)) =
      sv.hom.app (F.obj (G.obj K)) ≫ Vt.map (sf.hom.app (G.obj K)) ≫
        bt.app (rC.obj (G.obj K)) ≫ Ft'.map (su.inv.app (G.obj K)) ≫
          sf'.inv.app (U.obj (G.obj K)))
    (he : rC'.map e = su.hom.app (G.obj K) ≫ Ut.map (sg.hom.app K) ≫
      mt.app (rD.obj K) ≫ Gt'.map (sv.inv.app K) ≫ sg'.inv.app (V.obj K))
    (hc : rD.map (ad.counit.app K) = sf.hom.app (G.obj K) ≫
      Ft.map (sg.hom.app K) ≫ adt.counit.app (rD.obj K))
    (hc' : rD'.map (ad'.counit.app (V.obj K)) = sf'.hom.app (G'.obj (V.obj K)) ≫
      Ft'.map (sg'.hom.app (V.obj K)) ≫ adt'.counit.app (rD'.obj (V.obj K)))
    (ht : bt.app (Gt.obj (rD.obj K)) ≫ Ft'.map (mt.app (rD.obj K)) ≫
      adt'.counit.app (Vt.obj (rD.obj K)) = Vt.map (adt.counit.app (rD.obj K))) :
    beta.hom.app (G.obj K) ≫ F'.map e ≫ ad'.counit.app (V.obj K) =
      V.map (ad.counit.app K) := by
  apply rD'.map_injective
  simp only [Functor.map_comp]
  rw [hc']
  have hn : rD'.map (F'.map e) ≫ sf'.hom.app (G'.obj (V.obj K)) =
      sf'.hom.app (U.obj (G.obj K)) ≫ Ft'.map (rC'.map e) :=
    sf'.hom.naturality e
  rw [reassoc_of% hn]
  simp only [Functor.comp_obj]
  rw [he]
  apply (cancel_mono (sv.hom.app K)).1
  rw [hb]
  simp only [Functor.map_comp, Category.assoc, Iso.inv_hom_id_app_assoc]
  have hu : Ft'.map (su.inv.app (G.obj K)) ≫ Ft'.map (su.hom.app (G.obj K)) =
      𝟙 _ := by rw [← Ft'.map_comp, su.inv_hom_id_app, Ft'.map_id]
  have hg : Ft'.map (sg'.inv.app (V.obj K)) ≫
      Ft'.map (sg'.hom.app (V.obj K)) = 𝟙 _ := by
    rw [← Ft'.map_comp, sg'.inv_hom_id_app, Ft'.map_id]
  rw [reassoc_of% hu, reassoc_of% hg]
  have hcounit : Ft'.map (Gt'.map (sv.inv.app K)) ≫
      adt'.counit.app (rD'.obj (V.obj K)) =
      adt'.counit.app (Vt.obj (rD.obj K)) ≫ sv.inv.app K :=
    adt'.counit.naturality (sv.inv.app K)
  rw [reassoc_of% hcounit]
  simp only [Iso.inv_hom_id_app]
  slice_lhs 3 4 => exact (bt.naturality (sg.hom.app K)).symm
  simp only [Functor.comp_map, Functor.comp_obj, Category.assoc, Category.comp_id]
  rw [ht]
  rw [← Vt.map_comp, ← Vt.map_comp, ← hc]
  exact (sv.hom.naturality (ad.counit.app K)).symm

section Integral
variable [∀ x : X, Invertible (l : X.residueField x)]
  [∀ y : Y, Invertible (l : Y.residueField y)]
  [∀ x : X', Invertible (l : X'.residueField x)]
  [∀ y : Y', Invertible (l : Y'.residueField y)]
  (s : IntegralData l E b o q a)

/-- The total-limit realization equation, in adjunction form. Cancelling its invertible
unit is precisely the displayed unit/limit/inverse-unit formula.
Source: clause (3), R lim of e (blueprint: det-sp-tower-exceptional-bc). -/
@[irreducible] def IsLimitRealization (x : SpTowerShriek.OpenExchange l E b o)
    (hb : IsIso (SpTowerMate.beta l E b o q a x))
    (K : sfIntegralConstructibleCategory l E Y) : Prop :=
  HEq ((reconstructed l E b o q a s x hb K).hom ≫
      s.rX'.normalization.adjunction.unit.app
        (s.right'.obj ((constructibleIntegralPullback l E v).obj K)).obj)
    (s.rX'.normalization.adjunction.homEquiv _ _
      (((source l E b o q a s K).hom ≫
        (SpTowerMate.mate l E b o q a x hb).app ((red l E b q s.rY).obj K) ≫
        (target l E b o q a s K).inv).hom))

/-- Exact integral realization: beta is the unique reduction transport; the inverse
limit of the tower mate is invertible and is the specified integral counit transpose.
Source: clause (3) (blueprint: det-sp-tower-exceptional-bc). -/
@[irreducible] def IntegralConclusion (x : SpTowerShriek.OpenExchange l E b o)
    (hb : IsIso (SpTowerMate.beta l E b o q a x)) : Prop :=
  ∃ beta : SpIntegralAdjunction.support l E c s.support_closed ⋙
      constructibleIntegralPullback l E v ≅
    constructibleIntegralPullback l E u' ⋙
      SpIntegralAdjunction.support l E (c.ofIsPullback sq) s.support_closed',
    (∀ M : sfIntegralConstructibleCategory l E X,
      (red l E b q s.rY').map (beta.hom.app M) = exchangeReduction l E b o q a s x M) ∧
    (∀ beta' : SpIntegralAdjunction.support l E c s.support_closed ⋙
        constructibleIntegralPullback l E v ≅
      constructibleIntegralPullback l E u' ⋙
        SpIntegralAdjunction.support l E (c.ofIsPullback sq) s.support_closed',
      (∀ M : sfIntegralConstructibleCategory l E X,
        (red l E b q s.rY').map (beta'.hom.app M) =
          exchangeReduction l E b o q a s x M) → beta' = beta) ∧
    ∀ K : sfIntegralConstructibleCategory l E Y,
      IsIso (reconstructed l E b o q a s x hb K) ∧
      IsLimitRealization l E b o q a s x hb K ∧
      HEq (reconstructed l E b o q a s x hb K)
        (integralTranspose l E b o q a s beta K)
private def integralExchange (x : SpTowerShriek.OpenExchange l E b o)
    (hb : IsIso (SpTowerMate.beta l E b o q a x)) :
    SpIntegralAdjunction.support l E c s.support_closed ⋙
        constructibleIntegralPullback l E v ≅
      constructibleIntegralPullback l E u' ⋙
        SpIntegralAdjunction.support l E (c.ofIsPullback sq) s.support_closed' := by
  letI := hb
  let F := SpIntegralAdjunction.support l E c s.support_closed
  let F' := SpIntegralAdjunction.support l E (c.ofIsPullback sq) s.support_closed'
  let U := constructibleIntegralPullback l E u'
  let V := constructibleIntegralPullback l E v
  let Ft := SpTowerGluing.support l E b o q c a.support_closed
  let Ft' := SpTowerGluing.support l E b o q (c.ofIsPullback sq) a.support_closed'
  let Ut := SpTowerMate.U l E b o q a
  let Vt := SpTowerMate.V l E b o q a
  let e : (F ⋙ V) ⋙ red l E b q s.rY' ≅ (U ⋙ F') ⋙ red l E b q s.rY' :=
    Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft F s.pullComparison' ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight s.supportComparison Vt ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (red l E b q s.rX)
        (asIso (SpTowerMate.beta l E b o q a x)) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight s.pullComparison.symm Ft' ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft U s.supportComparison'.symm ≪≫
      (Functor.associator _ _ _).symm
  exact (s.rY'.fullyFaithful.whiskeringRight _).preimageIso e

private theorem integralExchange_reduction (x : SpTowerShriek.OpenExchange l E b o)
    (hb : IsIso (SpTowerMate.beta l E b o q a x))
    (M : sfIntegralConstructibleCategory l E X) :
    (red l E b q s.rY').map ((integralExchange l E b o q a s x hb).hom.app M) =
      exchangeReduction l E b o q a s x M := by
  unfold integralExchange exchangeReduction
  simp only [Functor.FullyFaithful.preimageIso_hom,
    Functor.FullyFaithful.whiskeringRight_preimage_app,
    Functor.FullyFaithful.map_preimage, Iso.trans_hom, NatTrans.comp_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Iso.symm_hom,
    asIso_hom, Category.id_comp, Category.comp_id]
  exact Category.id_comp _

private theorem reconstructed_counit (x : SpTowerShriek.OpenExchange l E b o)
    (hb : IsIso (SpTowerMate.beta l E b o q a x))
    (K : sfIntegralConstructibleCategory l E Y) :
    (integralExchange l E b o q a s x hb).hom.app (s.right.obj K) ≫
        (SpIntegralAdjunction.support l E (c.ofIsPullback sq) s.support_closed').map
          (reconstructed l E b o q a s x hb K) ≫
        s.adjunction'.counit.app ((constructibleIntegralPullback l E v).obj K) =
      (constructibleIntegralPullback l E v).map (s.adjunction.counit.app K) := by
  have := hb
  let F' := SpTowerGluing.support l E b o q (c.ofIsPullback sq) a.support_closed'
  let U := SpTowerMate.U l E b o q a
  let V := SpTowerMate.V l E b o q a
  let Kt := (red l E b q s.rY).obj K
  let e := reconstructed l E b o q a s x hb K
  have he : (red l E b q s.rX').map e =
      (source l E b o q a s K).hom ≫
        (SpTowerMate.mate l E b o q a x hb).app Kt ≫
          (target l E b o q a s K).inv := by
    unfold e reconstructed
    exact s.rX'.fullyFaithful.map_preimage _
  have ht : (SpTowerMate.beta l E b o q a x).app (a.right.obj Kt) ≫
      F'.map ((SpTowerMate.mate l E b o q a x hb).app Kt) ≫
        a.adjunction'.counit.app (V.obj Kt) = V.map (a.adjunction.counit.app Kt) := by
    have h := mateEquiv_counit a.adjunction a.adjunction'
      (TwoSquare.mk _ _ _ _ (@inv _ _ _ _ (SpTowerMate.beta l E b o q a x) hb)) Kt
    change F'.map ((SpTowerMate.mate l E b o q a x hb).app Kt) ≫
      a.adjunction'.counit.app (V.obj Kt) = _ at h
    rw [h]
    simp [V]
  have := s.rY'.fullyFaithful.faithful
  apply counit_transport (red l E b q s.rX) (red l E b q s.rY)
    (red l E b q s.rX') (red l E b q s.rY')
    _ _ _ _ _ _ _ _ _ _ _ _ s.adjunction s.adjunction' a.adjunction a.adjunction'
    s.supportComparison s.supportComparison' s.exceptionalComparison
    s.exceptionalComparison' s.pullComparison s.pullComparison'
    (SpTowerMate.beta l E b o q a x) (SpTowerMate.mate l E b o q a x hb)
    (integralExchange l E b o q a s x hb) K e
  · simpa only [exchangeReduction] using
      integralExchange_reduction l E b o q a s x hb (s.right.obj K)
  · simpa only [source, target, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom,
      Functor.mapIso_hom, Functor.mapIso_inv, Iso.app_hom, Iso.app_inv,
      Category.assoc, Kt] using he
  · exact s.counit K
  · exact s.counit' _
  · exact ht

private theorem reconstructed_isIso (x : SpTowerShriek.OpenExchange l E b o)
    (hb : IsIso (SpTowerMate.beta l E b o q a x))
    (hm : IsIso (SpTowerMate.mate l E b o q a x hb))
    (K : sfIntegralConstructibleCategory l E Y) :
    IsIso (reconstructed l E b o q a s x hb K) := by
  have := hm
  let e := (source l E b o q a s K) ≪≫
    asIso ((SpTowerMate.mate l E b o q a x hb).app ((red l E b q s.rY).obj K)) ≪≫
      (target l E b o q a s K).symm
  unfold reconstructed
  simpa only [Functor.FullyFaithful.preimageIso_hom, e, Iso.trans_hom,
    Iso.symm_hom, asIso_hom, Category.assoc] using
    (s.rX'.fullyFaithful.preimageIso e).isIso_hom

private theorem reconstructed_limit (x : SpTowerShriek.OpenExchange l E b o)
    (hb : IsIso (SpTowerMate.beta l E b o q a x))
    (K : sfIntegralConstructibleCategory l E Y) :
    IsLimitRealization l E b o q a s x hb K := by
  let t := (source l E b o q a s K).hom ≫
    (SpTowerMate.mate l E b o q a x hb).app ((red l E b q s.rY).obj K) ≫
      (target l E b o q a s K).inv
  have h : (red l E b q s.rX').map (reconstructed l E b o q a s x hb K) = t := by
    unfold reconstructed
    exact s.rX'.fullyFaithful.map_preimage t
  unfold IsLimitRealization
  apply heq_of_eq
  change (reconstructed l E b o q a s x hb K).hom ≫
    s.rX'.normalization.adjunction.unit.app _ =
      s.rX'.normalization.adjunction.homEquiv _ _ t.hom
  rw [← h]
  simpa only [Adjunction.homEquiv_unit, Functor.comp_map, Functor.id_map,
    red, SpIntegralAdjunction.reduce, SpIntegralAdjunction.reduction,
    ObjectProperty.lift_map, ObjectProperty.ι_map, ObjectProperty.ι_obj,
    ObjectProperty.homMk] using
    s.rX'.normalization.adjunction.unit.naturality
      (reconstructed l E b o q a s x hb K).hom

private theorem integralConclusion_of_data (x : SpTowerShriek.OpenExchange l E b o)
    (hb : IsIso (SpTowerMate.beta l E b o q a x))
    (hm : IsIso (SpTowerMate.mate l E b o q a x hb)) :
    IntegralConclusion l E b o q a s x hb := by
  unfold IntegralConclusion
  let beta := integralExchange l E b o q a s x hb
  refine ⟨beta, integralExchange_reduction l E b o q a s x hb, ?_, ?_⟩
  · intro beta' hbeta'
    apply Iso.ext
    apply NatTrans.ext
    funext M
    apply s.rY'.fullyFaithful.map_injective
    exact (hbeta' M).trans (integralExchange_reduction l E b o q a s x hb M).symm
  · intro K
    refine ⟨reconstructed_isIso l E b o q a s x hb hm K,
      reconstructed_limit l E b o q a s x hb K, ?_⟩
    apply heq_of_eq
    apply (s.adjunction'.homEquiv _ _).symm.injective
    unfold integralTranspose
    rw [Equiv.symm_apply_apply]
    change (SpIntegralAdjunction.support l E (c.ofIsPullback sq) s.support_closed').map
        (reconstructed l E b o q a s x hb K) ≫
      s.adjunction'.counit.app _ = _
    apply (cancel_epi (beta.hom.app (s.right.obj K))).1
    simpa only [Category.assoc, Iso.hom_inv_id_app_assoc] using
      reconstructed_counit l E b o q a s x hb K

end Integral

/-- Compact-support exchange and its exceptional counit mate are isomorphisms on
uniformly bounded constructible finite-Tor towers. The evaluations and all reductions
are the specified finite mates. Normalized inputs remain normalized. In the integral
case the reconstructed map is exactly the counit transpose of transported exchange.
Source: latest blueprint, sk-prop-sp-purity-bc-tower.md, clauses (1)--(3)
(blueprint: det-sp-tower-exceptional-bc).

Proof:
1. The existing tower_mate_evaluation_reduction supplies the actual exchange,
its finite evaluation and all mixed reduction laws.
2. finite_mates_and_source_normalized gives invertible finite counit mates.
The evaluation law and its comparison isomorphisms make every evaluated tower
mate invertible. Conservativity in b.calculus, transported by levelComparison,
and reflection through realization and the full inclusion prove invertibility.
3. The same finite criterion normalizes the source on normalized inputs.
Naturality of each derived reduction transfers normalization across the actual
mate isomorphism to the target.
4. integral_data_exists supplies the common integral coordinates. Whiskering
with fully faithful reduction is fully faithful: take the preimage of the whole
natural exchange isomorphism. Its reduction formula is exchangeReduction;
faithfulness gives uniqueness.
5. Reconstruct the conjugated tower mate by the inverse of reduction on Hom
sets. This is the hom of a preimage isomorphism. Naturality of the actual
normalization unit proves its unit/total-limit realization formula.
6. The tower mate-counit equation, together with the two integral counit
comparisons and naturality of the support/pullback comparisons, gives the
integral counit equation after reduction. Faithfulness and injectivity of the
primed adjunction transpose identify reconstructed with integralTranspose.
-/
theorem tower_exceptional_base_change
    (k : FiniteFieldDatum.{u}) (_hne : l ≠ k.p)
    (x : SpTowerShriek.OpenExchange l E b o)
    (X Y X' Y' : Over (Spec (CommRingCat.of k.k)))
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated Y.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    [IsSeparated X'.hom] [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
    [IsSeparated Y'.hom] [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom]
    (f : X ⟶ Y) (v : Y' ⟶ Y) (u' : X' ⟶ X) (f' : X' ⟶ Y')
    (sq : IsPullback u'.left f'.left f.left v.left)
    (d : ℕ) [SmoothOfRelativeDimension d f.left] (c : Compactification f.left) :
    ∃ a : SpTowerMate.Data l E b o q sq c,
    ∃ hb : IsIso (SpTowerMate.beta l E b o q a x),
    ∃ hfinite : ∀ (n : ℕ)
      (K : spFiniteConstructibleTorCategory Y.left (SpTowerShriek.R l E n)),
      IsIso ((SpTowerMate.finiteExchange l E b (sq := sq) (c := c) n).app
        ((a.levels.right n).obj K).obj),
      SpTowerMate.Laws l E b o q a x hb hfinite ∧
      IsIso (SpTowerMate.mate l E b o q a x hb) ∧
      (∀ K : SpTowerCalculus.C l E b q Y.left,
        IsSpNormalizedTower l E Y.left (q.abelian Y.left) K.obj →
          IsSpNormalizedTower l E X'.left (q.abelian X'.left)
              (((SpTowerMate.U l E b o q a).obj (a.right.obj K)).obj) ∧
            IsSpNormalizedTower l E X'.left (q.abelian X'.left)
              ((a.right'.obj ((SpTowerMate.V l E b o q a).obj K)).obj)) ∧
      (Module.finrank (Padic l) E = 1 →
        ∀ [∀ z : X.left, Invertible (l : X.left.residueField z)]
          [∀ z : Y.left, Invertible (l : Y.left.residueField z)]
          [∀ z : X'.left, Invertible (l : X'.left.residueField z)]
          [∀ z : Y'.left, Invertible (l : Y'.left.residueField z)],
        ∃ s : IntegralData l E b o q a, IntegralConclusion l E b o q a s x hb) := by
  obtain ⟨a, hb, hfinite, hlaws⟩ :=
    SpTowerMate.tower_mate_evaluation_reduction l E b o q k _hne x X Y X' Y'
      f v u' f' sq d c
  obtain ⟨hf, hn⟩ := finite_mates_and_source_normalized l E b o q k _hne
    X Y X' Y' f v u' f' sq d c a hfinite
  have hm := mate_isIso_of_finite l E b o q a x hb hfinite hlaws hf
  refine ⟨a, hb, hfinite, hlaws, hm, ?_, ?_⟩
  · intro K hK
    have := hm
    refine ⟨hn K hK, ?_⟩
    exact normalized_of_iso l E X'.left (q.abelian X'.left)
      ((SpTowerCalculus.inclusion l E b q X'.left).mapIso
        (asIso ((SpTowerMate.mate l E b o q a x hb).app K))) (hn K hK)
  · intro hrank _ _ _ _
    obtain ⟨s⟩ := integral_data_exists l E b o q k _hne X Y X' Y'
      f v u' f' sq d c a hrank
    exact ⟨s, integralConclusion_of_data l E b o q a s x hb hm⟩

end AlgebraicGeometry.ProEtale.SpExceptionalBaseChange
