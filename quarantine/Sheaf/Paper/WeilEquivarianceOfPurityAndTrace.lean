/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E7
-/
module

public import Sheaf.Paper.WeilPurityEquivarianceData
import Sheaf.Paper.FiniteGeometricPurityMate
import Sheaf.Paper.RationalWeilPurityNaturalityMate
import Sheaf.Paper.IntegralEquivarianceNaturality
import Sheaf.Paper.IntegralEquivarianceMate
import Sheaf.SecSmoothPurity.SmoothPurityNaturality

/-! # Geometric Frobenius equivariance of purity, counit and trace

The proof assembles purity naturality, the geometric counit mate, and compact-support
exchange naturality. All coefficient maps are specified in WeilPurityEquivarianceData.
(blueprint: thm-pur-weil-equivariance-of-purity-and-trace).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u uX uY vX vY
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures.PurityWeil

set_option allowUnsafeReducibility true in
attribute [local reducible] PurityFiniteSetting.Coefficient
  PurityFiniteSetting.smoothPurityPullback ProEtale.sfFixedDerivedPullback
  PurityFiniteSetting.geometricPurityF PurityFiniteSetting.compositionTwistShift
  ProEtale.rightDerivedLowerShriekOfCompactificationEtaleOrigin

private theorem threeSquares_of_equations {CX : Type uX} {CY : Type uY}
    [Category.{vX} CX] [Category.{vY} CY]
    (Q : CX ⥤ CX) (P : CY ⥤ CY) (F : CX ⥤ CY)
    {K : CY} {HK GK HPK GPK : CX}
    (phi : P.obj K ≅ K) (gamma : HK ≅ GK) (gammaP : HPK ≅ GPK)
    (b : Q.obj HK ≅ HPK) (hphi : HPK ≅ HK) (gphi : GPK ≅ GK)
    (epsilon : F.obj GK ⟶ K) (epsilonP : F.obj GPK ⟶ P.obj K)
    (BH : P.obj (F.obj HK) ⟶ F.obj (Q.obj HK))
    (BG : P.obj (F.obj GK) ⟶ F.obj (Q.obj GK))
    (hn : gammaP.hom ≫ gphi.hom = hphi.hom ≫ gamma.hom)
    (hm : BG ≫ F.map ((Q.mapIso gamma).inv ≫ b.hom ≫ gammaP.hom) ≫ epsilonP =
      P.map epsilon)
    (hc : F.map gphi.hom ≫ epsilon = epsilonP ≫ phi.hom)
    (hB : P.map (F.map gamma.hom) ≫ BG = BH ≫ F.map (Q.map gamma.hom)) :
    ThreeSquares Q P F phi gamma gammaP b hphi gphi epsilon BH BG := by
  have h₁ : Q.map gamma.hom ≫ (exceptionalStructure Q gamma gammaP b gphi).hom =
      (b ≪≫ hphi).hom ≫ gamma.hom := by
    simp only [exceptionalStructure, Iso.trans_hom, Iso.symm_hom,
      Functor.mapIso_inv, Category.assoc]
    rw [← Category.assoc (Q.map gamma.hom), ← Q.map_comp]
    rw [Iso.hom_inv_id, Q.map_id, Category.id_comp, hn]
  have h₂ : P.map epsilon ≫ phi.hom =
      (BG ≫ F.map (exceptionalStructure Q gamma gammaP b gphi).hom) ≫ epsilon := by
    calc
      _ = (BG ≫ F.map ((Q.mapIso gamma).inv ≫ b.hom ≫ gammaP.hom) ≫
          epsilonP) ≫ phi.hom := by rw [hm]
      _ = _ := by
        simp only [exceptionalStructure, Iso.trans_hom, Iso.symm_hom, Functor.map_comp,
          Category.assoc] at hc ⊢
        rw [hc]
  refine ⟨h₁, h₂, ?_⟩
  calc
    _ = P.map (F.map gamma.hom) ≫ P.map epsilon ≫ phi.hom := by
      rw [Functor.map_comp, Category.assoc]
    _ = P.map (F.map gamma.hom) ≫ BG ≫
        F.map (exceptionalStructure Q gamma gammaP b gphi).hom ≫ epsilon := by
      rw [h₂, Category.assoc]
    _ = (BH ≫ F.map (Q.map gamma.hom)) ≫
        F.map (exceptionalStructure Q gamma gammaP b gphi).hom ≫ epsilon := by
      rw [← Category.assoc (P.map (F.map gamma.hom)), hB]
    _ = _ := by
      simp only [Category.assoc]
      have hF := congrArg F.map h₁
      simp only [Functor.map_comp] at hF
      rw [← Category.assoc (F.map (Q.map gamma.hom)), hF]
      simp only [Category.assoc]

private theorem threeSquares_of_naturalityMate {CX : Type uX} {CY : Type uY}
    [Category.{vX} CX] [Category.{vY} CY]
    (Q : CX ⥤ CX) (P : CY ⥤ CY) (H : CY ⥤ CX)
    (F : CX ⥤ CY) (G : CY ⥤ CX) (adj : F ⊣ G)
    (gamma : ∀ K : CY, H.obj K ≅ G.obj K)
    (b : ∀ K : CY, Q.obj (H.obj K) ≅ H.obj (P.obj K))
    (B : F ⋙ P ≅ Q ⋙ F)
    (h : PurityNaturalityMate Q P H F G adj gamma b B)
    (K : CY) (phi : P.obj K ≅ K) :
    ThreeSquares Q P F phi (gamma K) (gamma (P.obj K)) (b K)
      (H.mapIso phi) (G.mapIso phi) (adj.counit.app K)
      (B.hom.app (H.obj K)) (B.hom.app (G.obj K)) := by
  apply threeSquares_of_equations Q P F phi (gamma K) (gamma (P.obj K)) (b K)
    (H.mapIso phi) (G.mapIso phi) (adj.counit.app K) (adj.counit.app (P.obj K))
  · exact h.1 phi.hom
  · have hm := h.2 K
    dsimp only [purityFrobeniusConjugate, Iso.trans_hom, Iso.symm_hom] at hm
    rw [hm]
    simp only [Iso.hom_inv_id_app_assoc]
  · exact adj.counit_naturality phi.hom
  · exact B.hom.naturality (gamma K).hom

section Geometry

variable (P : PurityFiniteSetting.{u})
  (X₀ Y₀ : Over (Spec (.of P.field.k₀)))
  [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]
  [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] [IsSeparated Y₀.hom]
  (f₀ : X₀ ⟶ Y₀)
  [IsSeparated f₀.left] [LocallyOfFiniteType f₀.left] [QuasiCompact f₀.left]
  (d : ℕ) [SmoothOfRelativeDimension d (P.frobeniusMap f₀)]

private theorem finiteGamma_naturality
    (M N : DerivedCategory (Sheaf (ProEt.topology (P.frobeniusFiber Y₀).left)
      (ModuleCat.{u + 1} P.Coefficient)))
    (hM : finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos
      (P.frobeniusFiber Y₀).left
      ((sfIntrinsicDerivedEquivalence (P.frobeniusFiber Y₀).left P.Ring).functor.obj M))
    (hN : finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos
      (P.frobeniusFiber Y₀).left
      ((sfIntrinsicDerivedEquivalence (P.frobeniusFiber Y₀).left P.Ring).functor.obj N))
    (a : M ⟶ N) :
    (P.geometricPurityIso (P.frobeniusMap f₀) d M hM).hom ≫
      (P.smoothPurityExceptionalOver (P.frobeniusMap f₀)
        ((P.frobeniusFiber Y₀).left ↘ Spec (.of P.field.k))).map a =
    (P.smoothPurityPullback (P.frobeniusMap f₀) ⋙
      P.compositionTwistShift (P.frobeniusFiber X₀).left d).map a ≫
      (P.geometricPurityIso (P.frobeniusMap f₀) d N hN).hom := by
  let E := sfIntrinsicDerivedEquivalence (P.frobeniusFiber Y₀).left P.Ring
  let R := (sfIntrinsicDerivedEquivalence (P.frobeniusFiber X₀).left P.Ring).functor
  let H := P.smoothPurityPullback (P.frobeniusMap f₀) ⋙
    P.compositionTwistShift (P.frobeniusFiber X₀).left d
  let G := P.smoothPurityExceptionalOver (P.frobeniusMap f₀)
    ((P.frobeniusFiber Y₀).left ↘ Spec (.of P.field.k))
  let tM := (P.smoothPurityReassociation (P.frobeniusFiber X₀).left d
    ((P.smoothPurityPullback (P.frobeniusMap f₀)).obj (E.inverse.obj (E.functor.obj M)))).hom ≫
    (P.existsUnique_smoothPurityTensorMap (P.frobeniusMap f₀) d
      (E.functor.obj M) hM).exists.choose
  let tN := (P.smoothPurityReassociation (P.frobeniusFiber X₀).left d
    ((P.smoothPurityPullback (P.frobeniusMap f₀)).obj (E.inverse.obj (E.functor.obj N)))).hom ≫
    (P.existsUnique_smoothPurityTensorMap (P.frobeniusMap f₀) d
      (E.functor.obj N) hN).exists.choose
  have hn := (P.smoothPurityMap_naturality_choice_independence
    (P.frobeniusMap f₀) d (E.functor.obj M) (E.functor.obj N) hM hN (E.functor.map a)).1
  have ht : tM ≫ G.map (E.inverse.map (E.functor.map a)) =
      H.map (E.inverse.map (E.functor.map a)) ≫ tN := by
    apply R.map_injective
    simpa only [E, R, H, G, tM, tN, PurityFiniteSetting.smoothPurityMap,
      PurityFiniteSetting.smoothPurityTensorMap, Functor.map_comp,
      PurityFiniteSetting.compositionTwistShift, Functor.comp_map, Functor.flip_obj_map,
      Category.assoc] using hn
  dsimp only [PurityFiniteSetting.geometricPurityIso, asIso,
    PurityFiniteSetting.geometricPurityMap]
  have hu := E.unitIso.hom.naturality a
  have hv := E.unitIso.inv.naturality a
  change a ≫ E.unitIso.hom.app N =
    E.unitIso.hom.app M ≫ E.inverse.map (E.functor.map a) at hu
  change E.inverse.map (E.functor.map a) ≫ E.unitIso.inv.app N =
    E.unitIso.inv.app M ≫ a at hv
  have hH := congrArg H.map hu
  simp only [Functor.map_comp] at hH
  have h : (H.map (E.unitIso.hom.app M) ≫ tM ≫ G.map (E.unitIso.inv.app M)) ≫
      G.map a = H.map a ≫
        (H.map (E.unitIso.hom.app N) ≫ tN ≫ G.map (E.unitIso.inv.app N)) := by
    calc
      _ = H.map (E.unitIso.hom.app M) ≫
          (tM ≫ G.map (E.inverse.map (E.functor.map a))) ≫ G.map (E.unitIso.inv.app N) := by
        simp only [Category.assoc, ← G.map_comp, hv]
      _ = _ := by
        rw [ht]
        simp only [Category.assoc]
        rw [reassoc_of% hH.symm]
  simpa only [E, H, G, tM, tN, Category.assoc] using h

private theorem finiteBeta_naturality
    (M N : DerivedCategory (Sheaf (ProEt.topology (P.frobeniusFiber X₀).left)
      (ModuleCat.{u + 1} P.Coefficient)))
    (hM : ProEtale.DerivedCategory.plusEtaleOrigin
      (ModuleCat.{u + 1} P.Coefficient) (P.frobeniusFiber X₀).left M)
    (hN : ProEtale.DerivedCategory.plusEtaleOrigin
      (ModuleCat.{u + 1} P.Coefficient) (P.frobeniusFiber X₀).left N)
    (a : M ⟶ N) :
    (P.smoothPurityPullback (P.frobeniusGaloisMap Y₀)).map
        ((P.geometricPurityF (P.frobeniusMap f₀) (P.frobeniusFiber Y₀).hom).map a) ≫
      P.geometricPurityB (P.frobeniusMap f₀) (P.frobeniusFiber Y₀).hom
        (P.frobeniusGaloisMap X₀) (P.frobeniusGaloisMap Y₀)
        (P.field.frobenius_square_cartesian X₀ Y₀ f₀).2.2.2.2.2.1 N =
    P.geometricPurityB (P.frobeniusMap f₀) (P.frobeniusFiber Y₀).hom
        (P.frobeniusGaloisMap X₀) (P.frobeniusGaloisMap Y₀)
        (P.field.frobenius_square_cartesian X₀ Y₀ f₀).2.2.2.2.2.1 M ≫
      (P.geometricPurityF (P.frobeniusMap f₀) (P.frobeniusFiber Y₀).hom).map
        ((P.smoothPurityPullback (P.frobeniusGaloisMap X₀)).map a) := by
  classical
  let A := ModuleCat.{u + 1} P.Coefficient
  let f := P.frobeniusMap f₀
  let aY := (P.frobeniusFiber Y₀).hom
  let F := P.geometricPurityF f aY
  let c := P.geometricPurityCompactification f aY
  let sq := (P.field.frobenius_square_cartesian X₀ Y₀ f₀).2.2.2.2.2.1
  let ix := ProEtale.leftDerivedUpperStarIsoMapDerivedCategory A (P.frobeniusGaloisMap X₀)
  let iy := ProEtale.leftDerivedUpperStarIsoMapDerivedCategory A (P.frobeniusGaloisMap Y₀)
  let D := (ProEtale.upperStar A (P.frobeniusGaloisMap X₀)).leftDerivedFunctor
  have hQM : ProEtale.DerivedCategory.plusEtaleOrigin A (P.frobeniusFiber X₀).left
      (D.obj M) := ObjectProperty.prop_of_iso _ (ix.app M).symm
        (P.geometricPurityPullbackOrigin (P.frobeniusGaloisMap X₀) M hM)
  have hQN : ProEtale.DerivedCategory.plusEtaleOrigin A (P.frobeniusFiber X₀).left
      (D.obj N) := ObjectProperty.prop_of_iso _ (ix.app N).symm
        (P.geometricPurityPullbackOrigin (P.frobeniusGaloisMap X₀) N hN)
  have hy := iy.inv.naturality (F.map a)
  have he := (ProEtale.rightDerivedLowerShriekOfCompactificationBaseChangeMap A sq c).naturality a
  have hi := (ProEtale.rightDerivedLowerShriekOfCompactificationEtaleOriginIso
    P.Coefficient (c.ofIsPullback sq) c).hom.naturality
      (X := ⟨D.obj M, hQM⟩) (Y := ⟨D.obj N, hQN⟩) (ObjectProperty.homMk (D.map a))
  have hx := congrArg F.map (ix.hom.naturality a)
  dsimp only [PurityFiniteSetting.geometricPurityB]
  rw [dif_pos hQM, dif_pos hQN]
  dsimp only [Functor.comp_map] at hy he hi hx
  simp only [Functor.map_comp] at hx
  let J := ProEtale.rightDerivedLowerShriekOfCompactification A (c.ofIsPullback sq)
  change (ProEtale.upperStar A (P.frobeniusGaloisMap Y₀)).leftDerivedFunctor.map
      (F.map a) ≫ _ = _ ≫ J.map (D.map a) at he
  change J.map (D.map a) ≫ _ = _ ≫ F.map (D.map a) at hi
  simp only [Category.assoc]
  rw [reassoc_of% hy, reassoc_of% he, reassoc_of% hi, hx]

private theorem finiteCounit_naturality
    (M N : DerivedCategory (Sheaf (ProEt.topology (P.frobeniusFiber Y₀).left)
      (ModuleCat.{u + 1} P.Coefficient)))
    (hM : ProEtale.DerivedCategory.plusEtaleOrigin
      (ModuleCat.{u + 1} P.Coefficient) (P.frobeniusFiber Y₀).left M)
    (hN : ProEtale.DerivedCategory.plusEtaleOrigin
      (ModuleCat.{u + 1} P.Coefficient) (P.frobeniusFiber Y₀).left N)
    (a : M ⟶ N) :
    (P.geometricPurityF (P.frobeniusMap f₀) (P.frobeniusFiber Y₀).hom).map
        ((P.smoothPurityExceptionalOver (P.frobeniusMap f₀)
          (P.frobeniusFiber Y₀).hom).map a) ≫
      P.geometricPurityCounit (P.frobeniusMap f₀) (P.frobeniusFiber Y₀).hom N =
    P.geometricPurityCounit (P.frobeniusMap f₀) (P.frobeniusFiber Y₀).hom M ≫ a := by
  classical
  let f := P.frobeniusMap f₀
  let aY := (P.frobeniusFiber Y₀).hom
  let := isNoetherian_of_locallyOfFiniteType aY
  let := isNoetherian_of_locallyOfFiniteType (f ≫ aY)
  let : HasCompactification f := inferInstance
  dsimp only [PurityFiniteSetting.geometricPurityCounit]
  rw [dif_pos hM.plus, dif_pos hN.plus]
  exact ProEtale.rightDerivedUpperShriekCounit_naturality f hM.plus hN.plus a

variable (c₀ : Compactification f₀.left)
  (S : ConstructibleExceptionalCoefficients.System P.coefficients.l P.coefficients.Qbar
    P.field P.coefficients.different (f := zlFiberMap P.field f₀))

/-- Purity, exceptional counit and normalized smooth trace are equivariant for every
strict geometric-Frobenius datum, at finite, completed integral, rational and common stages.
Source: current blueprint, sec-six-functors/sk-thm-sf-package,
thm-pur-weil-equivariance-of-purity-and-trace
(blueprint: thm-pur-weil-equivariance-of-purity-and-trace).

Proof:
1. Apply lem-pur-finite-geometric-purity-mate at finite coefficients and
   lem-pur-tower-geometric-purity-mate on coherent towers. The canonical counit mate e
   satisfies Q(Gamma) followed by e = b followed by Gamma at PK. Invert Q(Gamma) to
   identify e with the displayed inverse-purity composite E. These are whole-tower maps.
2. For phi : PK ≅ K, put a = b followed by H(phi), c = E followed by G(phi).
   Naturality of smooth purity (prop-pur-smooth-purity-naturality-cover at finite level,
   det-sp-tower-gamma on towers) gives Q(Gamma) followed by c = a followed by Gamma.
3. The adjunct-counit identity gives F(e) followed by epsilon at PK = inverse B at GK
   followed by P(epsilon). Counit naturality at phi then identifies B followed by F(c)
   followed by epsilon with P(epsilon) followed by phi. This is the second square.
4. Naturality of B and the first square identify B at HK followed by F(a) followed
   by F(Gamma) with P(F(Gamma)) followed by B at GK followed by F(c). Postcompose
   with epsilon and use step 3. Since trace = F(Gamma) followed by epsilon, this is
   the third square, with exactly the compact-support structures specified in the node.
5. Reduce an integral strict datum to its normalized tower using the pullback comparison
   and reconstruction units of det-sp-normalized-equivalence. Realize steps 1--4 by total
   inverse limit. The geometric comparison realization identifies b, Gamma, B, counit and
   the datum with their completed integral maps. The counit-preserving adjoint comparison
   identifies this Gamma with integralGamma (lem-pur-tower-trace-purity-comparison).
   This uses functoriality on whole towers, never faithfulness of separate evaluations.
6. Localize the integral naturality and mate equations for E; the rational-family
   identification and trace coherence identify the specified maps. A rational phi need
   not preserve an integral lattice: rational_weil_purity_naturality_mate treats every
   rational arrow by its scalar-fraction formula. For Qbar represent the datum and the
   equations over one common finite coefficient stage. Coefficient cocycles and canonical
   exchange/projection comparisons identify further extensions, so the equations descend
   to common-stage morphism classes. This proves all three squares at both field stages.
-/
theorem weilEquivarianceOfPurityAndTrace :
    FiniteClause P X₀ Y₀ f₀ d ∧
      IntegralClause P X₀ Y₀ f₀ d c₀ S ∧
      RationalClause P X₀ Y₀ f₀ d c₀ S ∧
      CommonClause P X₀ Y₀ f₀ d c₀ S := by
  let : SmoothOfRelativeDimension d (zlFiberMap P.field f₀) :=
    inferInstanceAs (SmoothOfRelativeDimension d (P.frobeniusMap f₀))
  obtain ⟨hr, hq⟩ := rational_weil_purity_naturality_mate P f₀ c₀ S d
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro K hK phi
    let f := P.frobeniusMap f₀
    let aY := (P.frobeniusFiber Y₀).hom
    let Q := P.smoothPurityPullback (P.frobeniusGaloisMap X₀)
    let R := P.smoothPurityPullback (P.frobeniusGaloisMap Y₀)
    let F := P.geometricPurityF f aY
    let G := P.smoothPurityExceptionalOver f aY
    let gamma := P.geometricPurityIso f d K hK
    let gammaP := P.geometricPurityIso f d (R.obj K) (P.geometricPurityInput Y₀ K hK)
    let b := P.geometricPuritySource X₀ Y₀ f₀ d K
    let B := P.geometricPurityB f aY (P.frobeniusGaloisMap X₀)
      (P.frobeniusGaloisMap Y₀)
      (P.field.frobenius_square_cartesian X₀ Y₀ f₀).2.2.2.2.2.1
    have hOrigin := P.geometricPurityOrigin _ K hK
    have hROrigin := P.geometricPurityPullbackOrigin (P.frobeniusGaloisMap Y₀) K hOrigin
    let := isNoetherian_of_locallyOfFiniteType aY
    let := isNoetherian_of_locallyOfFiniteType (f ≫ aY)
    let : HasCompactification f := inferInstance
    have hGOrigin : ProEtale.DerivedCategory.plusEtaleOrigin
        (ModuleCat.{u + 1} P.Coefficient) (P.frobeniusFiber X₀).left (G.obj K) :=
      ProEtale.plusEtaleOrigin_rightDerivedUpperShriek_obj f hOrigin.plus
    have hHOrigin : ProEtale.DerivedCategory.plusEtaleOrigin
        (ModuleCat.{u + 1} P.Coefficient) (P.frobeniusFiber X₀).left ((P.smoothPurityPullback f ⋙
          P.compositionTwistShift (P.frobeniusFiber X₀).left d).obj K) := by
      exact ObjectProperty.prop_of_iso _ gamma.symm hGOrigin
    apply threeSquares_of_equations Q R F phi gamma gammaP b _ _
      (P.geometricPurityCounit f aY K) (P.geometricPurityCounit f aY (R.obj K))
    · exact finiteGamma_naturality P X₀ Y₀ f₀ d _ _ _ _ phi.hom
    · have hm := (P.existsUnique_geometricPurityMate X₀ Y₀ f₀ K hK).choose_spec.1
      have hc := (P.finiteGeometricPurityMate X₀ Y₀ f₀ d K hK).2.2
      have hc' : (Q.mapIso gamma).inv ≫ b.hom ≫ gammaP.hom =
          P.geometricPurityMate X₀ Y₀ f₀ K hK := by
        simpa only [Q, gamma, b, gammaP, PurityFiniteSetting.geometricPurityIso,
          asIso_hom] using hc.symm
      rw [hc']
      exact hm
    · exact finiteCounit_naturality P X₀ Y₀ f₀ _ _ hROrigin hOrigin phi.hom
    · exact finiteBeta_naturality P X₀ Y₀ f₀ _ _ hHOrigin hGOrigin gamma.hom
  · obtain ⟨hn, hB⟩ := integralEquivariance_naturality P X₀ Y₀ f₀ d c₀ S
    intro K phi
    let op := S.ring.operation (zlGeometricCompactification P.field f₀ c₀)
      (.integral (AdicSmoothDualizing.fieldStage P))
    apply threeSquares_of_equations (integralP P X₀) (integralP P Y₀) op.F phi
      (integralGamma P X₀ Y₀ f₀ d c₀ S K)
      (integralGamma P X₀ Y₀ f₀ d c₀ S ((integralP P Y₀).obj K))
      (integralB P X₀ Y₀ f₀ d K) ((integralH P (P.frobeniusMap f₀) d).mapIso phi)
      (op.G.mapIso phi) (op.adjunction.counit.app K)
      (op.adjunction.counit.app ((integralP P Y₀).obj K))
    · exact hn phi.hom
    · rw [integralEquivariance_mate P X₀ Y₀ f₀ d c₀ S K]
      simp only [op, Iso.hom_inv_id_assoc]
    · exact (S.ring.operation (zlGeometricCompactification P.field f₀ c₀)
        (.integral (AdicSmoothDualizing.fieldStage P))).adjunction.counit_naturality phi.hom
    · exact hB (integralGamma P X₀ Y₀ f₀ d c₀ S K).hom
  · intro K phi
    exact threeSquares_of_naturalityMate _ _ _ _ _ _ _ _ _ hr K phi
  · intro K phi
    exact threeSquares_of_naturalityMate _ _ _ _ _ _ _ _ _ hq K phi

end Geometry
end WeilConjectures.PurityWeil
