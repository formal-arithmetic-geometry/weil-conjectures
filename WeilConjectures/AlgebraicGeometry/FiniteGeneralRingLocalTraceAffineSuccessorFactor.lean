/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.General.FiniteGeneralRingData
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Data
import WeilConjectures.AlgebraicGeometry.FiniteGeneralRingAffineSuccessorTransition
import WeilConjectures.AlgebraicGeometry.FiniteGeneralRingAffineLineStepStrength
import WeilConjectures.AlgebraicGeometry.FiniteGeneralRingAffineUnitPullback
import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryAffineLineTensorCounit
import WeilConjectures.AlgebraicGeometry.ProperProjectionFormula

/-! # Last-coordinate counit square with the preceding coefficient
Source: general-ring smooth purity, proof (3), ordered affine induction.
(blueprint: lem-sp-general-ring-integration-exponent-local-trace-affine-successor-factor).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.ProEtale

attribute [local implicit_reducible] affineTraceTower
set_option linter.auxLemma false in
attribute [local instance 100000] Etale.DerivedCategoryModule._proof_1
  Etale.DerivedCategoryModule._proof_2

private theorem tensor_counit_comparison
    {C D : Type*} [Category C] [Category D]
    (L : D ⥤ C) {RM RN : C ⥤ D} (am : L ⊣ RM) (an : L ⊣ RN)
    (H : C ⥤ C) (H' : D ⥤ D) (action : L ⋙ H ⟶ H' ⋙ L)
    {U K : C} (u : H.obj U ≅ K)
    (sM : H'.obj (RM.obj U) ≅ RM.obj (H.obj U))
    (sN : H'.obj (RN.obj U) ≅ RN.obj (H.obj U))
    (eU : RM.obj U ⟶ RN.obj U) (eK : RM.obj K ⟶ RN.obj K)
    (hact : IsIso (action.app (RM.obj U)))
    (hs : H'.map eU ≫ sN.hom ≫ RN.map u.hom =
      sM.hom ≫ RM.map u.hom ≫ eK)
    (heU : L.map eU ≫ an.counit.app U = am.counit.app U)
    (hm : action.app (RM.obj U) ≫ L.map sM.hom ≫ am.counit.app (H.obj U) =
      H.map (am.counit.app U))
    (hn : action.app (RN.obj U) ≫ L.map sN.hom ≫ an.counit.app (H.obj U) =
      H.map (an.counit.app U)) :
    L.map eK ≫ an.counit.app K = am.counit.app K := by
  have := hact
  let pM := sM.hom ≫ RM.map u.hom
  let pN := sN.hom ≫ RN.map u.hom
  have hm' := am.counit.naturality u.hom
  have hn' := an.counit.naturality u.hom
  simp only [Functor.comp_map, Functor.id_map] at hm' hn'
  have ha := action.naturality eU
  simp only [Functor.comp_map] at ha
  have hs' : H'.map eU ≫ pN = pM ≫ eK := by
    simpa only [pN, pM, Category.assoc] using hs
  have : IsIso pM := by dsimp only [pM]; infer_instance
  apply (cancel_epi (action.app (RM.obj U) ≫ L.map pM)).mp
  calc
    _ = action.app (RM.obj U) ≫ L.map (pM ≫ eK) ≫ an.counit.app K := by
      simp only [Functor.map_comp, Category.assoc]
    _ = action.app (RM.obj U) ≫ L.map (H'.map eU ≫ pN) ≫ an.counit.app K := by
      rw [hs']
    _ = H.map (L.map eU) ≫ action.app (RN.obj U) ≫ L.map pN ≫
        an.counit.app K := by
      simp only [Functor.map_comp, Category.assoc]
      rw [← reassoc_of% ha]
    _ = H.map (L.map eU) ≫ H.map (an.counit.app U) ≫ u.hom := by
      simp only [pN, Functor.map_comp, Category.assoc]
      rw [hn', reassoc_of% hn]
    _ = H.map (am.counit.app U) ≫ u.hom := by rw [← H.map_comp_assoc, heU]
    _ = action.app (RM.obj U) ≫ L.map pM ≫ am.counit.app K := by
      simp only [pM, Functor.map_comp, Category.assoc]
      rw [hm', reassoc_of% hm]
    _ = _ := by simp only [Category.assoc]

/-- The coefficient transition at a successor obeys the one-coordinate counit square
after the preceding affine transition.  This is the coefficient recursion and line
counit naturality calculation used by the ordered tower successor.
(blueprint: lem-sp-general-ring-integration-exponent-local-trace-affine-successor-factor).

Proof: first apply the unit comparison after pullback to the preceding tower stage.
The strength compatibility and the proved tensor counit squares extend this equation
to the preceding coefficient complex. Cancel the invertible tensor action to obtain
the coefficient counit square. Rewrite the successor transition by its proved
last-coordinate factorization. Counit naturality moves the preceding transition
past the last-coordinate counit; composing the coefficient square gives the result. -/
theorem finiteGeneralRingLocalTraceExponent_affine_successor_factor
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (M N : ℕ) (hMpos : 0 < M) (hNpos : 0 < N)
    (hM : (M : A) = 0) (hN : (N : A) = 0)
    (T : Scheme.{u}) [IsNoetherian T]
    (hMunit : IsUnit (M : Γ(T, ⊤))) (hNunit : IsUnit (N : Γ(T, ⊤)))
    (q : T.rootsOfUnitySheaf M ⟶ T.rootsOfUnitySheaf N)
    (b : Scheme.finiteEtaleTateLine T M A hM ≅
      Scheme.finiteEtaleTateLine T N A hN)
    (hb : FiniteGeneralRingKummerComparison A M N hM hN T q b)
    (tN : Etale.OrdinaryFiniteTwistTransport A N hN)
    (DN : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      Etale.OrdinaryFiniteP1Datum A N hN tN T hT)
    (tM : Etale.OrdinaryFiniteTwistTransport A M hM)
    (DM : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (M : Γ(T, ⊤))),
      Etale.OrdinaryFiniteP1Datum A M hM tM T hT)
    (d : ℕ) [IsNoetherian (affineTraceTower T d)]
    (eD : (Etale.affineTraceRight A M hM T d).obj
        (Etale.ordinaryFiniteUnit A T) ⟶
      (Etale.affineTraceRight A N hN T d).obj
        (Etale.ordinaryFiniteUnit A T))
    (heD : eD =
      (Etale.affineLinearCoefficientDescent A M hM tM T hMunit d).hom ≫
        (Etale.ordinaryFinitePullback A (affineTraceProjection T d)).map
          (finiteGeneralRingLevelPower A M N hM hN T b d).hom ≫
        (Etale.affineLinearCoefficientDescent A N hN tN T hNunit d).inv)
    (eSucc : (Etale.affineTraceRight A M hM T (d + 1)).obj
        (Etale.ordinaryFiniteUnit A T) ⟶
      (Etale.affineTraceRight A N hN T (d + 1)).obj
        (Etale.ordinaryFiniteUnit A T))
    (heSucc : eSucc =
      (Etale.affineLinearCoefficientDescent A M hM tM T hMunit (d + 1)).hom ≫
        (Etale.ordinaryFinitePullback A (affineTraceProjection T (d + 1))).map
          (finiteGeneralRingLevelPower A M N hM hN T b (d + 1)).hom ≫
        (Etale.affineLinearCoefficientDescent A N hN tN T hNunit (d + 1)).inv)
    (eLine : (Etale.affineTraceRight A M hM T 1).obj
        (Etale.ordinaryFiniteUnit A T) ⟶
      (Etale.affineTraceRight A N hN T 1).obj
        (Etale.ordinaryFiniteUnit A T))
    (_heLine : eLine =
      (Etale.affineLinearCoefficientDescent A M hM tM T hMunit 1).hom ≫
        (Etale.ordinaryFinitePullback A (affineTraceProjection T 1)).map
          (finiteGeneralRingLevelPower A M N hM hN T b 1).hom ≫
        (Etale.affineLinearCoefficientDescent A N hN tN T hNunit 1).inv)
    (_hline : (Etale.affineTraceLineLeft A T).map eLine ≫
        Etale.affineTraceCounit A N hN tN DN T hNunit 1 =
      Etale.affineTraceCounit A M hM tM DM T hMunit 1) :
    (Etale.affineTraceLineLeft A (affineTraceTower T d)).map eSucc ≫
        (Etale.affineTraceLineAdjunction A N hN tN (affineTraceTower T d)
          (affineTraceInvertible N T hNunit d)
          (DN (affineTraceTower T d)
            (affineTraceInvertible N T hNunit d))).counit.app
          ((Etale.affineTraceRightTower
            (fun r ↦ Etale.affineTraceLineRight A N hN (affineTraceTower T r)) d).obj
              (Etale.ordinaryFiniteUnit A T)) =
      (Etale.affineTraceLineAdjunction A M hM tM (affineTraceTower T d)
          (affineTraceInvertible M T hMunit d)
          (DM (affineTraceTower T d)
            (affineTraceInvertible M T hMunit d))).counit.app
          ((Etale.affineTraceRightTower
            (fun r ↦ Etale.affineTraceLineRight A M hM (affineTraceTower T r)) d).obj
              (Etale.ordinaryFiniteUnit A T)) ≫ eD := by
  let U := affineTraceTower T d
  let K := (Etale.affineTraceRight A M hM T d).obj (Etale.ordinaryFiniteUnit A T)
  let one := Etale.ordinaryFiniteUnit A U
  let dm := DM U (affineTraceInvertible M T hMunit d)
  let dn := DN U (affineTraceInvertible N T hNunit d)
  let am := Etale.affineTraceLineAdjunction A M hM tM U
    (affineTraceInvertible M T hMunit d) dm
  let an := Etale.affineTraceLineAdjunction A N hN tN U
    (affineTraceInvertible N T hNunit d) dn
  let e := finiteGeneralRingAffineLineStep A M N hM hN tM tN T hMunit hNunit b d
  have hu : (Etale.affineTraceLineLeft A U).map (e one) ≫ an.counit.app one =
      am.counit.app one :=
    finiteGeneralRingAffineUnit_pullback A M N hM hN tM tN T hMunit hNunit b d
      hMpos hNpos q hb DM DN
  have hs := finiteGeneralRingAffineLineStep_strength A M N hM hN tM tN T
    hMunit hNunit b d K
  have hAction : IsIso ((Etale.OrdinaryAffineTensorActions.lineActionNat A U K).app
      ((Etale.affineTraceLineRight A M hM U).obj one)) := by
    let V := (Etale.affineTraceLineRight A M hM U).obj one
    have : IsLocallyNoetherian (ProjectiveLine U) :=
      LocallyOfFiniteType.isLocallyNoetherian (ProjectiveLine U ↘ U)
    have : CompactSpace (ProjectiveLine U) :=
      QuasiCompact.compactSpace_of_compactSpace (ProjectiveLine U ↘ U)
    have : IsProper (ProjectiveLine U ↘ U) :=
      ProjectiveSpace.instIsProper (ULift (Fin 2)) U
    have hproper : IsIso (Etale.ordinaryFiniteProjection A (ProjectiveLine U ↘ U)
        ((Etale.affineTraceOpenLeft A U).obj V) K) :=
      Etale.isIso_proper_projection_formula_reordered A (ProjectiveLine U ↘ U) _ K
    have hopen : IsIso (Etale.OrdinaryAffineTensorActions.openAction A U
        ((Etale.ordinaryFinitePullback A (ProjectiveLine U ↘ U)).obj K) V) := by
      let HP := (Etale.ordinaryFinitePullback A (ProjectiveLine U ↘ U)).obj K
      let s1 := ((Etale.derivedTensorSymmetry (ModuleCat.{u + 1} A)
        (ProjectiveLine U)).app HP).app ((Etale.affineTraceOpenLeft A U).obj V)
      let s2 := ((Etale.derivedOpenImmersionLowerShriekProjectionIso
        (ModuleCat.{u + 1} A) (ProjectiveLine.affineChart U)).symm.app V).app HP
      let s3 := (Etale.affineTraceOpenLeft A U).mapIso
        (((Etale.derivedTensorSymmetry (ModuleCat.{u + 1} A)
          (AffineSpace PUnit.{u + 1} U)).app V).app
            ((Etale.ordinaryFinitePullback A (ProjectiveLine.affineChart U)).obj HP))
      exact (inferInstance : IsIso (s1 ≪≫ s2 ≪≫ s3).hom)
    change IsIso (Etale.ordinaryFiniteProjection A (ProjectiveLine U ↘ U)
        ((Etale.affineTraceOpenLeft A U).obj V) K ≫
      (Etale.ordinaryFinitePushforward A (ProjectiveLine U ↘ U)).map
        (Etale.OrdinaryAffineTensorActions.openAction A U
          ((Etale.ordinaryFinitePullback A (ProjectiveLine U ↘ U)).obj K) V))
    infer_instance
  have hw : (Etale.affineTraceLineLeft A U).map (e K) ≫ an.counit.app K =
      am.counit.app K :=
    tensor_counit_comparison (Etale.affineTraceLineLeft A U) am an
      ((Etale.ordinaryFiniteTensor A U).obj K)
      ((Etale.ordinaryFiniteTensor A (AffineSpace PUnit.{u + 1} U)).obj
        ((Etale.OrdinaryAffineTensorActions.linePull A U).obj K))
      (Etale.OrdinaryAffineTensorActions.lineActionNat A U K)
      (Etale.derivedTensorSingleUnitIso K)
      (Etale.OrdinaryAffineTensorActions.lineStrength A M hM U K one)
      (Etale.OrdinaryAffineTensorActions.lineStrength A N hN U K one)
      (e one) (e K) hAction hs hu
      (Etale.ordinaryAffineLine_tensorCounit A M hM tM U
        (affineTraceInvertible M T hMunit d) dm K one)
      (Etale.ordinaryAffineLine_tensorCounit A N hN tN U
        (affineTraceInvertible N T hNunit d) dn K one)
  have ht := finiteGeneralRingAffineSuccessorTransition A M N hM hN T hMunit
    hNunit b tN tM d eD heD eSucc heSucc
  rw [ht, Functor.map_comp, Category.assoc]
  have hn : (Etale.affineTraceLineLeft A U).map
        ((Etale.affineTraceLineRight A N hN U).map eD) ≫ an.counit.app _ =
      an.counit.app K ≫ eD := an.counit.naturality eD
  change (Etale.affineTraceLineLeft A U).map (e K) ≫
      (Etale.affineTraceLineLeft A U).map
        ((Etale.affineTraceLineRight A N hN U).map eD) ≫ an.counit.app _ = _
  rw [hn, ← Category.assoc, hw]

end AlgebraicGeometry.ProEtale
