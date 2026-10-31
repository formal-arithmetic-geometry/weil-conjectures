/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.DiagonalEtaleComparison.DiagonalEtaleSourceTransport
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.DiagonalEtaleComparison.DiagonalEtaleRestrictedDualizingData
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Diagonal.DiagonalExchangeNaturality
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Dnc.ComparisonPullbackDerivedCoherence
import all WeilConjectures.AlgebraicGeometry.Section.SectionExceptionalFibreCoherence
import all WeilConjectures.SmoothPurity.PurityFiniteSetting.DiagonalEtaleComparison.DiagonalEtaleSourceEndpoint

/-! # The alpha square over the restricted target

Source: diagonal-dualizing proof Steps 1--2; orientation-charts proof Step 3.
(blueprint: lem-pur-diagonal-etale-alpha-square).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting

attribute [local irreducible] Etale.upperStar Etale.lowerStar
  Etale.rightDerivedUpperShriek Etale.rightDerivedUpperShriekAdjunction
  ProEtale.upperStar ProEtale.comparisonUpperStar
  Functor.mapDerivedCategory Functor.rightDerivedFunctor conjugateIsoEquiv

open Etale in
private theorem section_factorization (A : Type (u + 1)) [CommRing A]
    {B T W Q R : Scheme.{u}} (e : T ⟶ B) (s : B ⟶ W)
    (a : Q ⟶ W) (t : R ⟶ Q) (sQ : T ⟶ Q) (sR : T ⟶ R)
    (hsQ : sQ ≫ a = e ≫ s) (hsR : sR ≫ t = sQ)
    (M : DerivedCategoryModule A W) (N : DerivedCategoryModule A Q)
    (N' : DerivedCategoryModule A R)
    (b : (ordinaryFinitePullback A a).obj M ≅ N)
    (c : (ordinaryFinitePullback A t).obj N ≅ N') :
    sectionCoherencePullbackIso A e s sQ a hsQ.symm M ≪≫
        (ordinaryFinitePullback A sQ).mapIso b ≪≫
        (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) sR t sQ hsR.symm).app N ≪≫
        (ordinaryFinitePullback A sR).mapIso c =
      sectionCoherencePullbackIso A e s sR (t ≫ a)
          (by rw [← Category.assoc, hsR, hsQ]) M ≪≫
        (ordinaryFinitePullback A sR).mapIso
          ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) t a).app M ≪≫
            (ordinaryFinitePullback A t).mapIso b ≪≫ c) := by
  have hn := (leftDerivedUpperStarComp (ModuleCat.{u + 1} A)
    sR t sQ hsR.symm).hom.naturality b.hom
  have hc := leftDerivedUpperStarComp_assoc'_app (ModuleCat.{u + 1} A)
    sR t a sQ (t ≫ a) (e ≫ s) hsR.symm rfl hsQ.symm M
  apply Iso.ext
  simp only [sectionCoherencePullbackIso, Iso.trans_hom, Iso.symm_hom,
    Iso.app_hom, Functor.mapIso_hom, Functor.map_comp, Category.assoc]
  simp only [Functor.comp_map] at hn
  dsimp only [ordinaryFinitePullback] at hn hc ⊢
  rw [reassoc_of% hn]
  erw [← reassoc_of% hc]

open Etale in
private theorem ambient_factorization (A : Type (u + 1)) [CommRing A]
    {B T W Q R : Scheme.{u}} (e : T ⟶ B) (p : W ⟶ B) (p' : R ⟶ T)
    (a : Q ⟶ W) (t : R ⟶ Q)
    (hv : (t ≫ a) ≫ p = p' ≫ e)
    (M : DerivedCategoryModule A B) (M' : DerivedCategoryModule A T)
    (N : DerivedCategoryModule A W) (NQ : DerivedCategoryModule A Q)
    (NR : DerivedCategoryModule A R)
    (b : (ordinaryFinitePullback A p).obj M ≅ N)
    (bQ : (ordinaryFinitePullback A a).obj N ≅ NQ)
    (bR : (ordinaryFinitePullback A p').obj M' ≅ NR)
    (l : (ordinaryFinitePullback A e).obj M ≅ M')
    (l' : (ordinaryFinitePullback A t).obj NQ ≅ NR)
    (hd : sectionCoherencePullbackIso A p' e t (a ≫ p)
          (hv.symm.trans (Category.assoc t a p)) M ≪≫
        (ordinaryFinitePullback A t).mapIso
          ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) a p).app M ≪≫
            (ordinaryFinitePullback A a).mapIso b ≪≫ bQ) ≪≫ l' =
      (ordinaryFinitePullback A p').mapIso l ≪≫ bR) :
    (ordinaryFinitePullback A (t ≫ a)).mapIso b ≪≫
        (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) t a).app N ≪≫
        (ordinaryFinitePullback A t).mapIso bQ ≪≫ l' =
      sectionCoherencePullbackIso A (t ≫ a) p p' e hv M ≪≫
        (ordinaryFinitePullback A p').mapIso l ≪≫ bR := by
  have hk := sectionPullback_endpoint A (t ≫ a) p p' e
    ((t ≫ a) ≫ p) (p' ≫ e) rfl hv hv.symm rfl M
  have hc := leftDerivedUpperStarComp_assoc'_app (ModuleCat.{u + 1} A)
    t a p (t ≫ a) (a ≫ p) (p' ≫ e) rfl rfl hv.symm M
  have hn := (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) t a).hom.naturality b.hom
  have hm : (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) t a).app
        ((ordinaryFinitePullback A p).obj M) =
      sectionCoherencePullbackIso A (t ≫ a) p p' e hv M ≪≫
        sectionCoherencePullbackIso A p' e t (a ≫ p)
          (hv.symm.trans (Category.assoc t a p)) M ≪≫
        (ordinaryFinitePullback A t).mapIso
          ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) a p).app M) := by
    apply Iso.ext
    dsimp only [sectionCoherencePullbackIso] at hk ⊢
    simp only [Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Functor.mapIso_hom,
      Category.assoc]
    have hkh := congrArg Iso.hom hk
    simp only [Iso.trans_hom, Iso.symm_hom, Iso.app_hom, NatTrans.comp_app] at hkh
    dsimp only [ordinaryFinitePullback] at hc ⊢
    rw [reassoc_of% hkh]
    simp only [Iso.hom_inv_id_app_assoc]
    rw [hc]
    simp only [Iso.inv_hom_id_app_assoc]
  apply Iso.ext
  have hdh := congrArg Iso.hom hd
  have hmh := congrArg Iso.hom hm
  simp only [Functor.comp_map] at hn
  simp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom,
    Functor.mapIso_trans, Category.assoc] at hdh hmh ⊢
  dsimp only [ordinaryFinitePullback] at hn hdh hmh ⊢
  rw [reassoc_of% hn, hmh]
  simpa only [Category.assoc] using congrArg
    ((sectionCoherencePullbackIso A (t ≫ a) p p' e hv M).hom ≫ ·) hdh

private theorem iso_span {C : Type*} [Category C] {S X Y A B T : C}
    (sj : S ≅ X) (sv : S ≅ Y) (a : X ≅ A) (b : Y ≅ B)
    (tj : A ≅ T) (tv : B ≅ T) (c : S ≅ T)
    (hj : sj ≪≫ a ≪≫ tj = c) (hv : sv ≪≫ b ≪≫ tv = c) :
    sj.symm ≪≫ sv ≪≫ b = a ≪≫ tj ≪≫ tv.symm := by
  calc
    _ = sj.symm ≪≫ ((sv ≪≫ b ≪≫ tv) ≪≫ tv.symm) := by
      simp only [Iso.trans_assoc, Iso.self_symm_id, Iso.trans_refl]
    _ = sj.symm ≪≫ ((sj ≪≫ a ≪≫ tj) ≪≫ tv.symm) := by rw [hv, ← hj]
    _ = _ := by simp only [← Iso.trans_assoc, Iso.symm_self_id, Iso.refl_trans]

private def ordinaryAlpha (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
    (d : ℕ) (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [SmoothOfRelativeDimension d f]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY] :=
  let := Dnc.compactifiable P f aY
  let := (P.comparedDiagonalBaseChange d f (f ≫ aY) aY rfl).2.2.2.1
  P.diagonalComparedRestriction f
    (asIso (Etale.dualizingComplexBaseChangeMap P.Coefficient
      (IsPullback.of_hasPullback f f).flip))

private theorem ordinary_alpha (P : PurityFiniteSetting.{u}) {U X Y : Scheme.{u}}
    [IsNoetherian U] [IsNoetherian X] [IsNoetherian Y]
    (d : ℕ) (g : X ⟶ Y) [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [SmoothOfRelativeDimension d g]
    (h : U ⟶ Y) [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    [SmoothOfRelativeDimension d h]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (e : U ⟶ X) [Etale e] [IsSeparated e] [QuasiCompact e]
    (w : e ≫ g = h) (N : Etale.EtaleCompactSupportNormalization P.Coefficient) :
    let := Dnc.compactifiable P g aY
    let := Dnc.compactifiable P h aY
    DiagonalEtaleComparison.sourceOrdinary P d g h aY e w N ≪≫
        (Etale.ordinaryFinitePullback P.Coefficient e).mapIso (ordinaryAlpha P d g aY) =
      ordinaryAlpha P d h aY ≪≫
        (Etale.sectionStructuralLocalityIso P.Coefficient e g h w).symm := by
  subst h
  let A := P.Coefficient
  let C := ModuleCat.{u + 1} A
  let p₁ := pullback.fst g g
  let p₂ := pullback.snd g g
  let a := pullback.fst p₁ e
  let b := pullback.snd p₁ e
  let t := DiagonalEtaleComparison.sourceLift d g (e ≫ g) e rfl
  let h := e ≫ g
  let r₁ := pullback.fst h h
  let r₂ := pullback.snd h h
  let s := Scheme.Hom.baseChangeSection p₁ (pullback.diagonal g)
    (pullback.diagonal_fst g) e
  let := P.noetherian (p₁ ≫ g ≫ aY)
  let := P.noetherian (b ≫ h ≫ aY)
  let := P.noetherian (r₁ ≫ h ≫ aY)
  let := Dnc.compactifiable P g aY
  let := Dnc.compactifiable P h aY
  let := Dnc.compactifiable P p₁ (g ≫ aY)
  let := Dnc.compactifiable P b (h ≫ aY)
  let := Dnc.compactifiable P r₁ (h ≫ aY)
  have ht : t ≫ b = r₁ := pullback.lift_snd _ _ _
  let : HasCompactification (t ≫ b) := HasCompactification.of_eq ht.symm
  have hs : pullback.diagonal h ≫ t = s :=
    (DiagonalEtaleComparison.sourceLift_geometry d g h e rfl).2.2.2
  have hv : (t ≫ a) ≫ p₂ = r₂ ≫ e := by
    rw [show t ≫ a = DiagonalEtaleComparison.selfMap d g h e rfl from
      pullback.lift_fst _ _ _]
    simp [DiagonalEtaleComparison.selfMap, p₂, r₂]
  have sqP := (IsPullback.of_hasPullback g g).flip
  have sqQ := IsPullback.of_hasPullback p₁ e
  have sq := sqQ.paste_horiz sqP
  have sqH := (IsPullback.of_hasPullback h h).flip
  have sqT : IsPullback r₂ t e (a ≫ p₂) := by
    have ho : IsPullback r₂ (t ≫ b) (e ≫ g) h := by rw [ht]; exact sqH
    exact ho.of_bot (by simpa only [Category.assoc] using hv.symm) sq
  let := (DiagonalEtaleComparison.sourceLift_geometry d g h e rfl).1
  let := (DiagonalEtaleComparison.sourceLift_geometry d g h e rfl).2.1
  let := (DiagonalEtaleComparison.sourceLift_geometry d g h e rfl).2.2.1
  let := Dnc.invertibleExponent P (p₁ ≫ g ≫ aY)
  let := Etale.isIso_rightDerivedUpperShriekBaseChangeMap_of_smoothOfRelativeDimension_general
    A p₁ d sqQ
  let := (Etale.isIso_dualizingComplexBaseChangeMap_iff A sqQ).2
    (inferInstanceAs (IsIso ((Etale.rightDerivedUpperShriekBaseChangeMap A sqQ).app (𝟙_ _))))
  let := (P.comparedDiagonalBaseChange d g (g ≫ aY) aY rfl).2.2.2.1
  let := (P.comparedDiagonalBaseChange d h (h ≫ aY) aY rfl).2.2.2.1
  let β := asIso (Etale.dualizingComplexBaseChangeMap A sqP)
  let βQ := asIso (Etale.dualizingComplexBaseChangeMap A sqQ)
  let βH := asIso (Etale.dualizingComplexBaseChangeMap A sqH)
  let E := Etale.sectionStructuralLocalityIso A e g h rfl
  let T := Etale.sectionStructuralLocalityIso A t b r₁ ht
  have hd := Etale.structural_locality_baseChange A e g t b h rfl r₁ ht
    h (a ≫ p₂) r₂ sq sqT sqH
  have hb := Etale.dualizing_base_comp A sqP sqQ
  rw [hb] at hd
  have hdI : Etale.sectionCoherencePullbackIso A r₂ e t (a ≫ p₂)
        (hv.symm.trans (Category.assoc t a p₂)) (Etale.dualizingComplex A g) ≪≫
      (Etale.ordinaryFinitePullback A t).mapIso
        ((Etale.leftDerivedUpperStarComp C a p₂).app _ ≪≫
          (Etale.ordinaryFinitePullback A a).mapIso β ≪≫ βQ) ≪≫ T =
      (Etale.ordinaryFinitePullback A r₂).mapIso E ≪≫ βH := by
    apply Iso.ext
    simpa only [Iso.trans_hom, Functor.mapIso_hom, Functor.mapIso_trans,
      Iso.app_hom, asIso_hom, Functor.map_comp, Category.assoc, β, βQ, βH, E, T,
      Etale.ordinaryFinitePullback, A, C, a, p₂] using hd
  have he := ambient_factorization A e p₂ r₂ a t hv
    (Etale.dualizingComplex A g) (Etale.dualizingComplex A h)
    (Etale.dualizingComplex A p₁) (Etale.dualizingComplex A b)
    (Etale.dualizingComplex A r₁) β βQ βH E T hdI
  have hs' : pullback.diagonal h ≫ (t ≫ a) = e ≫ pullback.diagonal g := by
    rw [← Category.assoc, hs]
    exact Scheme.Hom.baseChangeSection_fst p₁ (pullback.diagonal g)
      (pullback.diagonal_fst g) e
  have hx := section_inverse_exchange_naturality A e p₂ r₂ (t ≫ a)
    (pullback.diagonal g) (pullback.diagonal h) hv hs'
    (pullback.diagonal_snd g) (pullback.diagonal_snd h)
    (Etale.dualizingComplex A g) (Etale.dualizingComplex A h)
    (Etale.dualizingComplex A p₁) (Etale.dualizingComplex A r₁) β βH E
    ((Etale.leftDerivedUpperStarComp C t a).app _ ≪≫
      (Etale.ordinaryFinitePullback A t).mapIso βQ ≪≫ T) he
  have hy := section_factorization A e (pullback.diagonal g) a t s
    (pullback.diagonal h)
    (Scheme.Hom.baseChangeSection_fst p₁ (pullback.diagonal g)
      (pullback.diagonal_fst g) e) hs
    (Etale.dualizingComplex A p₁) (Etale.dualizingComplex A b)
    (Etale.dualizingComplex A r₁) βQ T
  have hy' : (DiagonalEtaleComparison.sourceOrdinary P d g h aY e rfl N).symm =
      Etale.sectionCoherencePullbackIso A e (pullback.diagonal g)
          (pullback.diagonal h) (t ≫ a) hs'.symm (Etale.dualizingComplex A p₁) ≪≫
        (Etale.ordinaryFinitePullback A (pullback.diagonal h)).mapIso
          ((Etale.leftDerivedUpperStarComp C t a).app _ ≪≫
            (Etale.ordinaryFinitePullback A t).mapIso βQ ≪≫ T) := by
    dsimp only [T] at hy ⊢
    rw [DiagonalEtaleComparison.locality_tensorMate_congr A N t b r₁ ht] at hy ⊢
    apply Iso.ext
    have hyh := congrArg Iso.hom hy
    simpa only [DiagonalEtaleComparison.sourceOrdinary, Dnc.sectionBaseChange,
      Etale.sectionCoherencePullbackIso, Iso.trans_symm, Iso.symm_symm_eq,
      Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.app_hom, Iso.app_inv,
      Functor.mapIso_trans, Functor.mapIso_hom, Functor.map_comp, Category.assoc,
      Etale.ordinaryFinitePullback, Etale.sectionInvariant, Etale.dualizingComplex,
      A, C, p₁, p₂, a, b, t, r₁, r₂, s, h, βQ, T] using hyh
  have hx' : (Etale.ordinaryFinitePullback A e).mapIso (ordinaryAlpha P d g aY) ≪≫ E =
      (DiagonalEtaleComparison.sourceOrdinary P d g h aY e rfl N).symm ≪≫
        ordinaryAlpha P d h aY := by
    rw [hy']
    simpa only [ordinaryAlpha, diagonalComparedRestriction, Etale.ordinaryFinitePullback,
      A, C, p₁, p₂, r₁, r₂, h, β, βH, Iso.trans_assoc] using hx
  change DiagonalEtaleComparison.sourceOrdinary P d g h aY e rfl N ≪≫
      (Etale.ordinaryFinitePullback A e).mapIso (ordinaryAlpha P d g aY) =
    ordinaryAlpha P d h aY ≪≫ E.symm
  calc
    _ = DiagonalEtaleComparison.sourceOrdinary P d g h aY e rfl N ≪≫
        (((Etale.ordinaryFinitePullback A e).mapIso (ordinaryAlpha P d g aY) ≪≫ E) ≪≫
          E.symm) := by simp only [Iso.trans_assoc, Iso.self_symm_id, Iso.trans_refl]
    _ = _ := by
      rw [hx']
      simp only [← Iso.trans_assoc, Iso.self_symm_id, Iso.refl_trans]

private theorem proetale_alpha (P : PurityFiniteSetting.{u}) {U X Y : Scheme.{u}}
    [IsNoetherian U] [IsNoetherian X] [IsNoetherian Y]
    (d : ℕ) (g : X ⟶ Y) [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [SmoothOfRelativeDimension d g]
    (h : U ⟶ Y) [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    [SmoothOfRelativeDimension d h]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (e : U ⟶ X) [Etale e] [IsSeparated e] [QuasiCompact e]
    (w : e ≫ g = h) (N : Etale.EtaleCompactSupportNormalization P.Coefficient) :
    let := Dnc.compactifiable P g aY
    let := Dnc.compactifiable P h aY
    DiagonalEtaleComparison.source P d g h aY e w N ≪≫
        (OrientationRefinement.pull P e).mapIso (P.affineDiagonalAlpha d g aY) ≪≫
        Dnc.pullComparison P e (Etale.dualizingComplex P.Coefficient g) ≪≫
        (ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} P.Coefficient) U).mapDerivedCategory.mapIso
            (Etale.sectionStructuralLocalityIso P.Coefficient e g h w) =
      P.affineDiagonalAlpha d h aY := by
  let := Dnc.compactifiable P g aY
  let := Dnc.compactifiable P h aY
  have ho := ordinary_alpha P d g h aY e w N
  have hn := Dnc.pullComparison_naturality P e (ordinaryAlpha P d g aY)
  have ho' : DiagonalEtaleComparison.sourceOrdinary P d g h aY e w N ≪≫
        (Etale.ordinaryFinitePullback P.Coefficient e).mapIso (ordinaryAlpha P d g aY) ≪≫
        Etale.sectionStructuralLocalityIso P.Coefficient e g h w =
      ordinaryAlpha P d h aY := by
    rw [← Iso.trans_assoc, ho]
    simp only [Iso.trans_assoc, Iso.symm_self_id, Iso.trans_refl]
  dsimp only [DiagonalEtaleComparison.source, affineDiagonalAlpha,
    OrientationRefinement.pull, Dnc.sourceEtale, ordinaryAlpha,
    Etale.ordinaryFinitePullback] at hn ho' ⊢
  simp only [Functor.mapIso_trans, Functor.mapIso_symm, Iso.trans_assoc,
    Iso.symm_self_id_assoc]
  rw [← Iso.trans_assoc _ _ ((ProEtale.comparisonUpperStar
    (ModuleCat.{u + 1} P.Coefficient) U).mapDerivedCategory.mapIso
      (Etale.sectionStructuralLocalityIso P.Coefficient e g h w)), hn]
  simp only [← Iso.trans_assoc, Iso.symm_self_id, Iso.refl_trans]
  simpa only [Functor.mapIso_trans, Iso.trans_assoc] using congrArg
    (fun z ↦ Dnc.sourceComparison P d (pullback.fst h h) (h ≫ aY)
      (pullback.diagonal h) ≪≫ (ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} P.Coefficient) U).mapDerivedCategory.mapIso z) ho'

/-- Naturality of the alpha factor, before target-open restriction or unit change.
Source: diagonal-dualizing proof Steps 1--2; orientation-charts proof Step 3.

Proof: work one side at a time, writing e:T→A, p:A→V and h=e≫p. Put
Wp=A×_V A, Q=Wp×_A T, with a:Q→Wp, b:Q→T and q=a≫p2. The self-product
map factors as t:Wh→Q followed by a, where t is sourceLift. Its geometry lemma
gives the Cartesian square (p2h,t,e,q), and (q,b,p,h) is the pasted self-product
and base-change square. Apply source-etale/base-change interchange to e,p,t,b
with base h and upper arrows q,p2h. This compares the pulled locality for e
followed by the h self-product mate with the pulled outer mate followed by
locality for t. The outer mate is the composite of the p self-product mate and
the mate for (a,b,p1,e), by dualizing exchange pasting.
The two resulting rectangles have the same outer counit mate. Pull their equality
along the common source diagonal, invert the self-product mates, and use the
second-projection section identity to cancel the interior pullback compositors.
Transport through the specified site comparisons. For each side this identifies
source followed by pulled-back alpha with common-source alpha followed by inverse
normalized locality. Composing the inverse jO equation with the vO equation cancels
the common-source alpha and gives precisely restrictedDualizingTransport. No rho,
coefficient-unit comparison, deformation, normal bundle, or integration occurs.
The base-change and section identities apply in rank zero and on empty schemes.
(blueprint: lem-pur-diagonal-etale-alpha-square). -/
theorem diagonalEtaleAlphaSquare (P : PurityFiniteSetting.{u})
    {X Z Y : Scheme.{u}} (d : ℕ) (f : X ⟶ Y) (g : Z ⟶ Y)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [SmoothOfRelativeDimension d f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [SmoothOfRelativeDimension d g]
    [IsNoetherian X] [IsNoetherian Z] [IsNoetherian Y]
    [HasCompactification f] [HasCompactification g]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (V : Y.affineOpens)
    (H : P.AffineDiagonalGeometry f aY d V)
    (K : P.AffineDiagonalGeometry g aY d V)
    (N : Etale.EtaleCompactSupportNormalization P.Coefficient)
    (U : Scheme.{u}) [IsNoetherian U]
    (j : U ⟶ X) [Etale j] [IsSeparated j] [LocallyOfFiniteType j] [QuasiCompact j]
    (v : U ⟶ Z) [Etale v] [IsSeparated v] [LocallyOfFiniteType v] [QuasiCompact v]
    (w : v ≫ g = j ≫ f)
    [HasCompactification (j ≫ f)] [HasCompactification (v ≫ g)]
    (O : U.Opens) (jO : O.toScheme ⟶ (f ⁻¹ᵁ V.1).toScheme)
    (vO : O.toScheme ⟶ (g ⁻¹ᵁ V.1).toScheme)
    (hj : jO ≫ (f ⁻¹ᵁ V.1).ι = O.ι ≫ j)
    (hv : vO ≫ (g ⁻¹ᵁ V.1).ι = O.ι ≫ v) :
    let s := DiagonalEtaleComparison.sourceTransport P d f g aY V H K N U j v w
      O jO vO hj hv
    let L := DiagonalEtaleComparison.restrictedDualizingTransport P f g aY V N U j v w
      O jO vO hj hv
    s.hom ≫ (OrientationRefinement.pull P vO).map
        (OrientationRefinement.alpha P g aY d V K).hom =
      (OrientationRefinement.pull P jO).map
        (OrientationRefinement.alpha P f aY d V H).hom ≫ L.hom := by
  let := H.smoothDimension
  let := K.smoothDimension
  let := P.noetherian (V.1.ι ≫ aY)
  let := P.noetherian ((f ∣_ V.1) ≫ V.1.ι ≫ aY)
  let := P.noetherian ((g ∣_ V.1) ≫ V.1.ι ≫ aY)
  let := P.noetherian (O.ι ≫ j ≫ f ≫ aY)
  have : Etale (jO ≫ (f ⁻¹ᵁ V.1).ι) := by rw [hj]; infer_instance
  have : Etale jO := Etale.of_comp jO (f ⁻¹ᵁ V.1).ι
  have : Etale (vO ≫ (g ⁻¹ᵁ V.1).ι) := by rw [hv]; infer_instance
  have : Etale vO := Etale.of_comp vO (g ⁻¹ᵁ V.1).ι
  have : IsSeparated (jO ≫ (f ⁻¹ᵁ V.1).ι) := by rw [hj]; infer_instance
  have : IsSeparated jO := IsSeparated.of_comp jO (f ⁻¹ᵁ V.1).ι
  have : IsSeparated (vO ≫ (g ⁻¹ᵁ V.1).ι) := by rw [hv]; infer_instance
  have : IsSeparated vO := IsSeparated.of_comp vO (g ⁻¹ᵁ V.1).ι
  have : QuasiCompact jO := inferInstance
  have : QuasiCompact vO := inferInstance
  have : SmoothOfRelativeDimension 0 jO :=
    (Etale.iff_smoothOfRelativeDimension_zero jO).mp inferInstance
  let h := jO ≫ (f ∣_ V.1)
  have hdim : SmoothOfRelativeDimension (0 + d) h :=
    inferInstanceAs (SmoothOfRelativeDimension (0 + d) (jO ≫ (f ∣_ V.1)))
  have : SmoothOfRelativeDimension d h :=
    Eq.mp (congrArg (fun n ↦ SmoothOfRelativeDimension n h) (Nat.zero_add d)) hdim
  have he : vO ≫ (g ∣_ V.1) = h := by
    apply (cancel_mono V.1.ι).mp
    dsimp only [h]
    rw [Category.assoc, Category.assoc, morphismRestrict_ι, morphismRestrict_ι,
      ← Category.assoc, hv, ← Category.assoc, hj]
    simp only [Category.assoc, w]
  let := Dnc.compactifiable P (f ∣_ V.1) (V.1.ι ≫ aY)
  let := Dnc.compactifiable P (g ∣_ V.1) (V.1.ι ≫ aY)
  let := Dnc.compactifiable P h (V.1.ι ≫ aY)
  let ν := (ProEtale.comparisonUpperStar
    (ModuleCat.{u + 1} P.Coefficient) O.toScheme).mapDerivedCategory
  let Ej := Etale.sectionStructuralLocalityIso P.Coefficient jO (f ∣_ V.1) h rfl
  let Ev := Etale.sectionStructuralLocalityIso P.Coefficient vO (g ∣_ V.1) h he
  let Tj := Dnc.pullComparison P jO _ ≪≫ ν.mapIso Ej
  let Tv := Dnc.pullComparison P vO _ ≪≫ ν.mapIso Ev
  let sj := DiagonalEtaleComparison.source P d (f ∣_ V.1) h (V.1.ι ≫ aY) jO rfl N
  let sv := DiagonalEtaleComparison.source P d (g ∣_ V.1) h (V.1.ι ≫ aY) vO he N
  have hjA : sj ≪≫ (OrientationRefinement.pull P jO).mapIso
        (OrientationRefinement.alpha P f aY d V H) ≪≫ Tj =
      P.affineDiagonalAlpha d h (V.1.ι ≫ aY) :=
    proetale_alpha P d (f ∣_ V.1) h (V.1.ι ≫ aY) jO rfl N
  have hvA : sv ≪≫ (OrientationRefinement.pull P vO).mapIso
        (OrientationRefinement.alpha P g aY d V K) ≪≫ Tv =
      P.affineDiagonalAlpha d h (V.1.ι ≫ aY) :=
    proetale_alpha P d (g ∣_ V.1) h (V.1.ι ≫ aY) vO he N
  have hs : DiagonalEtaleComparison.sourceTransport P d f g aY V H K N U j v w
      O jO vO hj hv = sj.symm ≪≫ sv := rfl
  have hL : DiagonalEtaleComparison.restrictedDualizingTransport P f g aY V N U j v w
      O jO vO hj hv = Tj ≪≫ Tv.symm := by
    dsimp only [Tj, Tv, Ej, Ev]
    rw [DiagonalEtaleComparison.locality_tensorMate_congr P.Coefficient N jO
      (f ∣_ V.1) h rfl]
    rw [DiagonalEtaleComparison.locality_tensorMate_congr P.Coefficient N vO
      (g ∣_ V.1) h he]
    simp only [Iso.trans_symm, Functor.mapIso_trans,
      Iso.trans_assoc, eqToIso_refl, Iso.trans_refl]
    dsimp only [DiagonalEtaleComparison.restrictedDualizingTransport, ν]
    simp only [Functor.mapIso_trans, Functor.mapIso_symm, Iso.trans_symm,
      Iso.trans_assoc, Functor.mapIso_symm]
    congr 3
  have hi := iso_span sj sv
    ((OrientationRefinement.pull P jO).mapIso (OrientationRefinement.alpha P f aY d V H))
    ((OrientationRefinement.pull P vO).mapIso (OrientationRefinement.alpha P g aY d V K))
    Tj Tv _ hjA hvA
  dsimp only
  rw [hs, hL]
  simpa only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Category.assoc] using
    congrArg Iso.hom hi

end WeilConjectures.PurityFiniteSetting
