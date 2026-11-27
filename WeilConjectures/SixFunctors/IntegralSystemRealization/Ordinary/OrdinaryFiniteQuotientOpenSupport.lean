/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurCompactSupport.IntegralCompactSupportCoefficientData
import WeilConjectures.SmoothPurity.Completed.CompletedPullbackTensorComparison
import WeilConjectures.AlgebraicGeometry.ProEtale.Open.ProEtaleOpenSlicePresentation
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
import all WeilConjectures.Algebra.Homology.ProperBaseChange.OpenImmersionTensorPiece

/-! # Finite quotient preserves ordinary open support

## References

* [Stacks, Tag 03DI]
* [Stacks, Tag 03EK]
* [Stacks, Tag 0E8I]
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralSystemRealization
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

attribute [-instance] WeilConjectures.integralOperationsSiteSmall
  CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

private local instance (W : Scheme.{u}) : EssentiallySmall.{u + 1} W.ProEt :=
  WeilConjectures.integralOperationsSiteSmall.{u, u} W
private local instance (W : Scheme.{u}) :
    HasSheafify (ProEt.topology W) CommRingCat.{u + 1} :=
  WeilConjectures.integralCoefficientRingSheafify.{u, u} W
private local instance (W : Scheme.{u}) :
    HasSheafify (ProEt.topology W) AddCommGrpCat.{u + 1} :=
  WeilConjectures.integralCoefficientAbSheafify.{u, u} W
private local instance (W : Scheme.{u}) :
    (ProEt.topology W).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  WeilConjectures.integralCoefficientAbLocallyBijective.{u, u} W

attribute [local irreducible] Functor.leftAdjoint CategoryTheory.constantSheaf
  completedIntegralCommRingSheafUnrestricted
  completedIntegralCoefficientSheafUnrestricted

private def finiteCoefficients (n : ℕ) : PurCompactSupport.Coefficients.{u} where
  ring := fun (W : Scheme.{u}) ↦ (constantSheaf (ProEt.topology W) CommRingCat.{u + 1}).obj
    (CommRingCat.of (ULift.{u + 1} (finiteCoefficientRing l E (n + 1))))
  pull f := proEtaleConstantRingComparison f (finiteCoefficientRing l E (n + 1))

private theorem finiteDirect_eq {X Y : Scheme.{u}} (j : X ⟶ Y) (n : ℕ) :
    proEtaleRingModuleDirectImage j ((finiteCoefficients l E n).ring Y)
      ((finiteCoefficients l E n).ring X) ((finiteCoefficients l E n).pull j) =
    coefficientProEtaleModuleDirectImage.{u, u} j
      (CommRingCat.of (ULift.{u + 1} (finiteCoefficientRing l E (n + 1)))) := by
  have hm : proEtaleRingDirectImageMap j ((finiteCoefficients l E n).ring Y)
      ((finiteCoefficients l E n).ring X) ((finiteCoefficients l E n).pull j) =
      coefficientProEtaleDirectRingMap.{u, u} j
        (CommRingCat.of (ULift.{u + 1} (finiteCoefficientRing l E (n + 1)))) := by
    let a := proEtaleSheafAdjunction j CommRingCat.{u + 1}
    change a.homEquiv _ _ ((a.homEquiv _ _).symm _) = _
    exact (a.homEquiv _ _).apply_symm_apply _
  unfold proEtaleRingModuleDirectImage coefficientProEtaleModuleDirectImage
  rw [hm]
  rfl

private def finitePullIso {X Y : Scheme.{u}} (j : X ⟶ Y) (n : ℕ) :
    integralOperationsLevelPullback l E j n ≅
      proEtaleRingModulePullback j ((finiteCoefficients l E n).ring Y)
        ((finiteCoefficients l E n).ring X) ((finiteCoefficients l E n).pull j) :=
  (coefficientProEtaleModuleAdjunction.{u, u} j
    (CommRingCat.of (ULift.{u + 1} (finiteCoefficientRing l E (n + 1))))).leftAdjointUniq
      ((proEtaleRingModuleAdjunction j ((finiteCoefficients l E n).ring Y)
        ((finiteCoefficients l E n).ring X) ((finiteCoefficients l E n).pull j)).ofNatIsoRight
          (eqToIso (finiteDirect_eq l E j n)))

private theorem projection_square {X Y : Scheme.{u}} (j : X ⟶ Y) (n : ℕ) :
    ((PurCompactSupport.completed l E).pull j).hom ≫
        completedIntegralCommRingProjectionUnrestricted l E X n =
      (proEtaleSheafInverseImage j CommRingCat.{u + 1}).map
        (completedIntegralCommRingProjectionUnrestricted l E Y n) ≫
          ((finiteCoefficients l E n).pull j).hom := by
  let adj := proEtaleSheafAdjunction j CommRingCat.{u + 1}
  dsimp only [PurCompactSupport.completed, finiteCoefficients]
  change (adj.homEquiv _ _).symm _ ≫ _ = _ ≫ (adj.homEquiv _ _).symm _
  rw [← adj.homEquiv_naturality_right_symm]
  erw [← adj.homEquiv_naturality_left_symm]
  exact congrArg (adj.homEquiv _ _).symm
    ((sfCompletedCoefficientMap_existsUnique l E j).exists.choose_spec n)

/-- A single quotient of an extended module is in the finite open essential image. -/
theorem ordinaryFiniteQuotientOpenSupport {X Y : Scheme.{u}}
    (j : X ⟶ Y) [IsOpenImmersion j] (n : ℕ)
    (L : normalizedDVRModules l E X n ⥤ normalizedDVRModules l E Y n)
    (adj : L ⊣ integralOperationsLevelPullback l E j n)
    (M : scalarReductionSource l E X) :
    IsIso (adj.counit.app ((unrestrictedIntegralReductionFunctor l E Y n).obj
      ((PurCompactSupport.openExtension (PurCompactSupport.completed l E) j).obj M))) := by
  let R := PurCompactSupport.completed l E
  let S := finiteCoefficients l E n
  let π (W : Scheme.{u}) := completedIntegralCommRingProjectionUnrestricted l E W n
  let ai := PurCompactSupport.openAdjunction R j
  let az := PurCompactSupport.openAdjunction S j
  let ep := finitePullIso l E j n
  let hs := projection_square l E j n
  let t : scalarReductionRestriction l E Y n ⋙
      proEtaleRingModulePullback j (R.ring Y) (R.ring X) (R.pull j) ≅
      integralOperationsLevelPullback l E j n ⋙ scalarReductionRestriction l E X n :=
    @asIso _ _ _ _ (proEtaleRingRestrictionPullbackInv j (R.ring Y) (S.ring Y)
      (R.ring X) (S.ring X) (π Y) (π X) (R.pull j) (S.pull j) hs)
      (proEtaleRingRestrictionPullbackInv_isIso j (R.ring Y) (S.ring Y)
        (R.ring X) (S.ring X) (π Y) (π X) (R.pull j) (S.pull j) hs) ≪≫
        Functor.isoWhiskerRight ep.symm (scalarReductionRestriction l E X n)
  let e := ((ai.comp (pullbackTensorFiniteAdjunction l E Y n)).ofNatIsoRight t).leftAdjointUniq
    ((pullbackTensorFiniteAdjunction l E X n).comp adj)
  obtain ⟨q, ⟨hq⟩⟩ := proEtaleOpen_slicePresentation j (S.ring Y) (S.ring X) (S.pull j)
  let Ls := SheafOfModules.localizedModuleExtension.{u} (S.ring Y) (ProEt.mk j)
  let ads := SheafOfModules.localizedModuleAdjunctionIndependent (S.ring Y) (ProEt.mk j)
  have := SheafOfModules.localizedUnit_isIso j (S.ring Y)
  have : Ls.Full := ads.fullyFaithfulLOfIsIsoUnit.full
  have : Ls.Faithful := ads.fullyFaithfulLOfIsIsoUnit.faithful
  have : q.functor.Full := q.fullyFaithfulFunctor.full
  have : q.functor.Faithful := q.fullyFaithfulFunctor.faithful
  have hfull : (q.functor ⋙ Ls).Full := Functor.Full.comp q.functor Ls
  have hfaithful : (q.functor ⋙ Ls).Faithful := Functor.Faithful.comp q.functor Ls
  let el : L ≅ q.functor ⋙ Ls := ((adj.ofNatIsoRight ep).leftAdjointUniq az) ≪≫ hq
  have : L.Full := @Functor.Full.of_iso _ _ _ _ _ _ hfull el.symm
  have : L.Faithful := @Functor.Faithful.of_iso _ _ _ _ _ _ hfaithful el.symm
  exact adj.isIso_counit_app_of_iso (e.app M)

end WeilConjectures.IntegralSystemRealization
