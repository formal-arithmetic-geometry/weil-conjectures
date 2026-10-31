/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedTateIntegralTowerData
import all WeilConjectures.AlgebraicGeometry.LisseCompletedPointwiseComparison
import all WeilConjectures.AlgebraicGeometry.PurTwistSheafLocallyFree
import all WeilConjectures.AlgebraicGeometry.IntegralCanonicalTruncations
import all WeilConjectures.AlgebraicGeometry.AdicCoefficientDatumSupplement
import WeilConjectures.Algebra.Homology.LineUnboundedDerivedTensor
import WeilConjectures.AlgebraicGeometry.PurTwistRootLocalModels

/-! A pre-tower for the strict ordinary Tate quotient construction.

The cocycle equation is kept separate from the other fields so that the
construction and its coherence can be proved independently.
(blueprint: lem-pur-strict-tate-tensor-tower-data-pre)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry.Etale.FiniteSmoothPurity
namespace AlgebraicGeometry.Scheme.PurityIntegralTower

structure StrictTateTensorTowerPre (T : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) where
  tower : DerivedCategory (pbcTowers T (pbcAdicCompletion T d))
  level : ∀ n : ℕ, DerivedCategory (pbcModules T ((pbcAdicRings T d).obj (op n)))
  evaluation : ∀ n : ℕ,
    (pbcDerivedRestrict (pbcAdicProjection T d n)).obj (level n) ≅
      (pbcTowerEvaluation T (pbcAdicCompletion T d) n).obj tower
  normalization : ∀ (b a : ℕ) (hab : a ≤ b),
    (pbcDerivedExtend (pbcAdicQuotient T d b a hab)).obj (level b) ≅ level a
  transition : ∀ (b a : ℕ) (hab : a ≤ b),
    (pbcDerivedRestrict (pbcAdicProjection T d b)).map
        (adicTowerSemilinearTransition T d level normalization b a hab) ≫
      (pbcDerivedRestrictComp (pbcAdicProjection T d b)
        (pbcAdicQuotient T d b a hab) (pbcAdicProjection T d a)
        (pbcAdicProjection_comp T d b a hab)).hom.app (level a) ≫
      (evaluation a).hom =
    (evaluation b).hom ≫
      (pbcTowerTransition T (pbcAdicCompletion T d) b a hab).app tower

def StrictTateTensorTowerPre.Cocycle
    {T : Scheme.{u}} {A : Type (u + 1)} [CommRing A]
    {d : AdicCoefficientDatum A} (P : StrictTateTensorTowerPre T d) : Prop :=
  ∀ (c b a : ℕ) (hab : a ≤ b) (hbc : b ≤ c),
    adicTowerSemilinearTransition T d P.level P.normalization c a
        (hab.trans hbc) =
      adicTowerSemilinearTransition T d P.level P.normalization c b hbc ≫
        (pbcDerivedRestrict (pbcAdicQuotient T d c b hbc)).map
          (adicTowerSemilinearTransition T d P.level P.normalization b a hab) ≫
        (pbcDerivedRestrictComp (pbcAdicQuotient T d c b hbc)
          (pbcAdicQuotient T d b a hab)
          (pbcAdicQuotient T d c a (hab.trans hbc))
          (pbcAdicQuotient_comp T d c b a hab hbc)).hom.app (P.level a)

def StrictTateTensorTowerPre.toAdicTower
    {T : Scheme.{u}} {A : Type (u + 1)} [CommRing A]
    {d : AdicCoefficientDatum A}
    (P : StrictTateTensorTowerPre T d)
    (hc : P.Cocycle) :
    AdicTower T d :=
  { tower := P.tower
    level := P.level
    evaluation := P.evaluation
    normalization := P.normalization
    transition := P.transition
    cocycle := hc }

attribute [local irreducible] HasDerivedCategory.standard completedAdicChangeData

private theorem integralRoot_line (T : Scheme.{u}) (ell : ℕ) [Fact ell.Prime]
    (hT : IsUnit (ell : Γ(T, ⊤))) :
    (integralRoot T ell).IsFiniteLocallyFreeOfRank 1 := by
  classical
  let (x : T) : Invertible (ell : T.residueField x) :=
    (show IsUnit (ell : T.residueField x) from by
      simpa only [map_natCast] using hT.map (T.evaluation ⊤ x (by trivial)).hom).invertible
  obtain ⟨I, U, f, hc, ht⟩ := (purTwistRootLocalModels T ell).2.1
  apply rank_one_of_cover (integralRoot T ell)
  refine ⟨I, U, f, hc, fun i ↦ ?_⟩
  let c := (adicLisseForget T).mapIso (completionIso T ell)
  let ci := ((ProEt.topology T).overPullback RingCat (U i)).mapIso c
  let E := AlgebraicGeometry.ProEtale.CompletedLisse.restrictionEquivalence ci
  exact ⟨E.functor.mapIso (ht i).some ≪≫
    (AlgebraicGeometry.ProEtale.CompletedLisse.restrictionUnitIso ci).symm⟩

private theorem integralLine_flat (T : Scheme.{u}) (ell : ℕ) [Fact ell.Prime]
    (hT : IsUnit (ell : Γ(T, ⊤))) (d : ℕ) :
    SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1} (J := ProEt.topology T)
      (R := pbcAdicCompletion T (datum.{u} ell)) (integralLine T ell d) := by
  let : EssentiallySmall.{u + 1} T.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  let R : Sheaf (ProEt.topology T) CommRingCat.{u + 1} :=
    pbcAdicCompletion T (datum.{u} ell)
  let := SheafOfModules.isMonoidal_W_independentCoefficients.{u + 1, u, u + 1} R
  let := SheafOfModules.monoidalCategory.{u, u + 1, u + 1} R
  have hroot := integralRoot_line T ell hT
  let := hroot
  have hr := (SheafOfModules.LineUnbounded.line_unbounded_derived_tensor.{u, 0, u + 2}
    T R (integralRoot T ell)).1
  have hf (d : ℕ) : ObjectProperty.flat (integralLine T ell d) := by
    induction d with
    | zero => exact ObjectProperty.prop_unit (ObjectProperty.flat (A := pbcModules T R))
    | succ d ih =>
      exact ObjectProperty.prop_tensor ih (SheafOfModules.flat_to_cat.{u + 1, u, u + 1} R _ hr)
  exact (exactFunctor _ _).prop_of_iso
    (SheafOfModules.siteSheafTensorRightIso.{u + 1, u, u + 1}
      R (integralLine T ell d)).symm (hf d).2

private def integralLine_singleReduction (T : Scheme.{u}) (ell : ℕ) [Fact ell.Prime]
    (hT : IsUnit (ell : Γ(T, ⊤))) (d n : ℕ) :
    (pbcDerivedExtend (pbcAdicProjection T (datum.{u} ell) n)).obj
        ((DerivedCategory.singleFunctor _ (-(2 * (d : ℤ)))).obj (integralLine T ell d)) ≅
      (DerivedCategory.singleFunctor _ (-(2 * (d : ℤ)))).obj (quotientLine T ell n d) :=
  extend_single_iso T _ _ _ (integralLine_flat T ell hT d)

private def strictTower_ordinaryComparison (T : Scheme.{u}) (ell : ℕ)
    [Fact ell.Prime] (d : ℕ) :
    completedReductionModuleTower T (datum.{u} ell) (integralLine T ell d) ≅
      strictTower T ell d := by
  let B := pbcAdicCompletion T (datum.{u} ell)
  let R := pbcAdicRings T (datum.{u} ell)
  let π : (Functor.const ℕᵒᵖ).obj B ⟶ R :=
    { app := fun n ↦ pbcAdicProjection T (datum.{u} ell) n.unop
      naturality := fun _ _ f ↦ (limit.w R f).symm }
  have hs (n : ℕ) : localReductionStep T B R π n =
      completedReductionTransition T (datum.{u} ell) (n + 1) n (Nat.le_succ n) := by
    apply ((localReductionStep_exists T B R π n).unique)
    · exact (localReductionStep_exists T B R π n).exists.choose_spec
    · intro M V b x
      exact (completedReductionTransition_exists T (datum.{u} ell)
        (n + 1) n (Nat.le_succ n)).exists.choose_spec M V b x
  let F := completedReductionModuleTower T (datum.{u} ell) (integralLine T ell d)
  let G := strictTower T ell d
  let η : F ⟶ G := NatTrans.ofOpSequence (fun _ ↦ 𝟙 _) (by
    intro n
    simp only [Category.comp_id, Category.id_comp]
    change (completedReductionModuleTower T (datum.{u} ell) (integralLine T ell d)).map
        (homOfLE (Nat.le_succ n)).op =
      ((Functor.ofOpSequence (fun n ↦ localReductionStep T B R π n)).map
        (homOfLE (Nat.le_succ n)).op).app (integralLine T ell d)
    rw [Functor.ofOpSequence_map_homOfLE_succ]
    simp only [completedReductionModuleTower, Functor.ofOpSequence_map_homOfLE_succ]
    rw [hs])
  exact NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun f ↦ η.naturality f)

set_option linter.unusedVariables false in
/-- The strict quotient construction supplies every pre-tower field and the
single-complex comparisons; only the cocycle calculation is omitted here.

Proof source: smooth-purity transport, normalized Tate tower, Steps 2--3.
The quotient-linear levels are obtained by ordinary tensor balancing on the
locally free root line, and exact single-complex evaluation identifies them
with the displayed quotient lines. The strict tower is used as the tower
component, with its projection evaluations and quotient normalizations.
(blueprint: lem-pur-strict-tate-tensor-tower-data-pre)
-/
theorem strictTateTensorTower_pre
    (T : Scheme.{u}) [IsNoetherian T] (ell : ℕ) [Fact ell.Prime]
    (hT : IsUnit (ell : Γ(T, ⊤))) (d : ℕ) :
    ∃ (P : StrictTateTensorTowerPre T (datum.{u} ell))
      (q : ∀ n : ℕ, P.level n ≅
        (_root_.DerivedCategory.singleFunctor _ (-(2 * (d : ℤ)))).obj
          (quotientLine T ell n d)),
      P.tower = strictDerivedTower T ell d := by
  let K : PbcCompletedDerived T (datum.{u} ell) :=
    (DerivedCategory.singleFunctor _ (-(2 * (d : ℤ)))).obj (integralLine T ell d)
  let M := pbcReductionAdicTower T (datum.{u} ell) K
  have ht : M.tower ≅ strictDerivedTower T ell d := by
    let q : ℤ := -(2 * (d : ℤ))
    let C := (CochainComplex.singleFunctor _ q).obj (integralLine T ell d)
    have hk := (single_kflat_iff_flat T (integralLine T ell d) q).2
      (integralLine_flat T ell hT d)
    haveI := towerCounit_isIso T (datum.{u} ell) C hk
    exact (completedReductionTower T (datum.{u} ell)).mapIso
        ((DerivedCategory.singleFunctorIsoCompQ _ q).app (integralLine T ell d)) ≪≫
      asIso (completedReductionTowerComplexCounit T (datum.{u} ell) C) ≪≫
      DerivedCategory.Q.mapIso
        ((HomologicalComplex.singleMapHomologicalComplex
          (completedReductionModuleTowerFunctor T (datum.{u} ell)) (.up ℤ) q).app
            (integralLine T ell d)) ≪≫
      ((DerivedCategory.singleFunctorIsoCompQ _ q).app _).symm ≪≫
      (DerivedCategory.singleFunctor _ q).mapIso (strictTower_ordinaryComparison T ell d)
  refine ⟨{ tower := strictDerivedTower T ell d
            level := M.level
            evaluation := fun n ↦ M.evaluation n ≪≫
              (pbcTowerEvaluation T (pbcAdicCompletion T (datum.{u} ell)) n).mapIso ht
            normalization := M.normalization
            transition := ?_ }, fun n ↦ integralLine_singleReduction T ell hT d n, rfl⟩
  intro b a hab
  dsimp only [Iso.trans_hom, Functor.mapIso_hom]
  have h := congrArg
    (fun f ↦ f ≫ (pbcTowerEvaluation T (pbcAdicCompletion T (datum.{u} ell)) a).map ht.hom)
    (M.transition b a hab)
  simpa only [Category.assoc,
    (pbcTowerTransition T (pbcAdicCompletion T (datum.{u} ell)) b a hab).naturality ht.hom]
    using h

end AlgebraicGeometry.Scheme.PurityIntegralTower
