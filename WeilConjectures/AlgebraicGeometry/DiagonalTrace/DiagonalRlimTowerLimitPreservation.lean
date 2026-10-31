/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.DiagonalTowerTraceCoefficients
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.DiagonalRlimForgetPullback
import all WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Realization.DiagonalRealizationPullback
import all WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficientTwistsSupplement
import all WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Completed.CompletedCoefficientRootLineComparison
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.BottomFiniteRootUnitIsIso
import all WeilConjectures.AlgebraicGeometry.Native.NativeIntegralTateTowerLimit
import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteTowerLimit

/-! # Preservation of the specified ordinary endpoint limits -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.DiagonalTrace
open SpTowerClasses
open scoped CategoryTheory.Obj CategoryTheory.MonObj

private theorem forget_preserves (l : ℕ) [Fact l.Prime] (T : Scheme.{u}) :
    PreservesLimitsOfShape ℕᵒᵖ (diagonalForget l T) := by
  have : PreservesLimitsOfSize.{0, 0} (diagonalForget l T) :=
    (diagonalScalarAdjunction l T).rightAdjoint_preservesLimits
  infer_instance

private theorem forget_reflects (l : ℕ) [Fact l.Prime] (T : Scheme.{u}) :
    ReflectsLimitsOfShape ℕᵒᵖ (diagonalForget l T) := by
  let := forget_preserves l T
  let : (diagonalForget l T).ReflectsIsomorphisms := by
    unfold diagonalForget
    infer_instance
  exact reflectsLimitsOfShape_of_reflectsIsomorphisms

private theorem pull_preserves_of_forget (l : ℕ) [Fact l.Prime]
    {X S : Scheme.{u}} (f : X ⟶ S) (H : DiagonalSystems l S)
    [PreservesLimit (H ⋙ diagonalForget l S) (upperStar AddCommGrpCat.{u + 1} f)] :
    PreservesLimit H (upperStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) f) := by
  let FS := diagonalForget l S
  let FX := diagonalForget l X
  let G := upperStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) f
  let A := upperStar AddCommGrpCat.{u + 1} f
  let := forget_preserves l S
  let := forget_preserves l X
  let := forget_reflects l X
  let : PreservesLimit H (FS ⋙ A) := inferInstance
  let : PreservesLimit H (G ⋙ FX) :=
    preservesLimit_of_natIso H (diagonalRlimForgetPullback l f).some.symm
  exact preservesLimit_of_reflects_of_preserves G FX

private theorem sheafCompose_preserves_countable
    {C D : Type (u + 2)} [Category.{u + 1} C] [Category.{u + 1} D]
    [HasLimitsOfShape ℕᵒᵖ C] [HasLimitsOfShape ℕᵒᵖ D]
    (T : Scheme.{u}) (F : C ⥤ D) [(Scheme.ProEt.topology T).HasSheafCompose F]
    [PreservesLimitsOfShape ℕᵒᵖ F] :
    PreservesLimitsOfShape ℕᵒᵖ (sheafCompose (Scheme.ProEt.topology T) F) := by
  let J := Scheme.ProEt.topology T
  let : PreservesLimitsOfShape ℕᵒᵖ
      (sheafCompose J F ⋙ sheafToPresheaf J D) :=
    inferInstanceAs (PreservesLimitsOfShape ℕᵒᵖ
      (sheafToPresheaf J C ⋙ (Functor.whiskeringRight _ _ _).obj F))
  exact preservesLimitsOfShape_of_reflects_of_preserves _ (sheafToPresheaf J D)

private theorem coefficient_ab_preserves (l : ℕ) [Fact l.Prime]
    {X S : Scheme.{u}} (f : X ⟶ S) :
    PreservesLimit (Scheme.purTwistZlTower S l ⋙
      sheafCompose (Scheme.ProEt.topology S)
        ((forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) ⋙
          forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1}))
      (upperStar AddCommGrpCat.{u + 1} f) := by
  let C := Scheme.purTwistZlTower S l
  let RS := sheafCompose (Scheme.ProEt.topology S) (forget CommRingCat.{u + 1})
  let RX := sheafCompose (Scheme.ProEt.topology X) (forget CommRingCat.{u + 1})
  let AS := sheafCompose (Scheme.ProEt.topology S) (forget AddCommGrpCat.{u + 1})
  let AX := sheafCompose (Scheme.ProEt.topology X) (forget AddCommGrpCat.{u + 1})
  let U := sheafCompose (Scheme.ProEt.topology S)
    ((forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) ⋙
      forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})
  let P := Scheme.proEtaleSheafInverseImage f (Type (u + 1))
  let R := Scheme.proEtaleSheafInverseImage f CommRingCat.{u + 1}
  let A := upperStar AddCommGrpCat.{u + 1} f
  let := sheafCompose_preserves_countable S (forget CommRingCat.{u + 1})
  let := sheafCompose_preserves_countable X (forget CommRingCat.{u + 1})
  let := sheafCompose_preserves_countable S (forget AddCommGrpCat.{u + 1})
  let := sheafCompose_preserves_countable X (forget AddCommGrpCat.{u + 1})
  let := sheafCompose_preserves_countable S
    ((forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) ⋙
      forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})
  let Q := DiagonalCoefficients.residueTower.{u} l
  have (n : ℕᵒᵖ) : NeZero (l ^ (n.unop + 1)) :=
    ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have (n : ℕᵒᵖ) : Finite (Q.obj n) := by
    change Finite (ULift (ZMod (l ^ (n.unop + 1))))
    infer_instance
  let := Scheme.proEtaleSheafInverseImage_preserves_finite_tower f Q
  let : PreservesLimit C R :=
    preservesLimit_of_iso_diagram R (DiagonalCoefficients.residueTowerIso l S)
  let : PreservesLimit C (R ⋙ RX) := inferInstance
  let : PreservesLimit C (RS ⋙ P) :=
    preservesLimit_of_natIso C (ringPullbackForgetIso f)
  let : PreservesLimit (C ⋙ RS) P :=
    preservesLimit_of_preserves_limit_cone
      (isLimitOfPreserves RS (limit.isLimit C))
      (isLimitOfPreserves (RS ⋙ P) (limit.isLimit C))
  let : PreservesLimit ((C ⋙ U) ⋙ AS) P :=
    inferInstanceAs (PreservesLimit (C ⋙ RS) P)
  let : PreservesLimit (C ⋙ U) (AS ⋙ P) := inferInstance
  let : PreservesLimit (C ⋙ U) (A ⋙ AX) :=
    preservesLimit_of_natIso (C ⋙ U) (abelianForgetInverseImageIso f).symm
  let : ReflectsLimitsOfShape ℕᵒᵖ AX := reflectsLimitsOfShape_of_reflectsIsomorphisms
  exact preservesLimit_of_reflects_of_preserves A AX

private theorem root_ab_preserves (l : ℕ) [Fact l.Prime]
    {X S : Scheme.{u}} (f : X ⟶ S)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : S, Invertible (l : S.residueField y)] :
    PreservesLimit (roots l S) (upperStar AddCommGrpCat.{u + 1} f) := by
  let E := DiagonalCoefficients.bottomField l
  let T := spIntegralTwistSystem S l E
  let U := Mod.forget
    (C := Sheaf (Scheme.ProEt.topology S) AddCommGrpCat.{u + 1})
    (D := Sheaf (Scheme.ProEt.topology S) AddCommGrpCat.{u + 1})
    (condensedRingObj (Profinite.padicIntegersRingObj.{u} l E.1) S)
  let a : roots l S ⟶ T ⋙ U := NatTrans.ofOpSequence
    (fun n ↦ (Mod.freeForgetAdjunction
      (condensedRingObj (spEllPointRingObj l E n) S)).unit.app
        (Scheme.proEtaleRootsOfUnitySheaf S (l ^ (n + 1)))) (by
      intro n
      dsimp only [T, U, roots, Functor.comp_map, spIntegralTwistSystem,
        Scheme.proEtaleRootsOfUnityTower]
      rw [Functor.ofOpSequence_map_homOfLE_succ,
        Functor.ofOpSequence_map_homOfLE_succ]
      have ht := (spIntegralLevelTransition_existsUnique S l E n).exists.choose_spec
      change (spIntegralLevelTransition S l E n).hom = _ at ht
      change _ = _ ≫ (spIntegralLevelTransition S l E n).hom
      rw [ht]
      exact (DiagonalCoefficients.freeUnit_tensorMap _ _).symm)
  let : ∀ n, IsIso (a.app n) :=
    fun n ↦ DiagonalCoefficients.bottomFiniteRootUnit_isIso l S n.unop
  let : IsIso a := NatIso.isIso_of_isIso_app a
  let : PreservesLimit (T ⋙ U) (upperStar AddCommGrpCat.{u + 1} f) :=
    preservesLimit_of_preserves_limit_cone (isLimitOfPreserves U (limit.isLimit T))
      (spIntegralTwist_inverseImage_isLimit f l E).some
  exact preservesLimit_of_iso_diagram (upperStar AddCommGrpCat.{u + 1} f) (asIso a).symm

/-- Inverse image preserves the two ordinary limits occurring in the endpoint comparison.

Source: blueprint coefficient proof (3), quotient and root limit comparisons.
The coefficient tower is the additive image of the finite constant residue-ring
tower. Ring inverse image preserves its limit by the profinite coefficient theorem.
Ring and abelian forgetting commute with inverse image after forgetting to sets,
and these functors preserve and reflect limits, so abelian inverse image preserves
the additive coefficient limit. The root tower is isomorphic, by the finite root
units for the bottom coefficient field, to the underlying native integral Tate
tower; its limit is preserved by the proved native Tate-limit theorem. The
normalized coefficientForget and lineForget isomorphisms transport these two
assertions to the given towers. Finally constant scalar
forgetting commutes with inverse image, preserves limits and reflects limits,
so both assertions lift to fixed scalar module sheaves.
(blueprint: new-sfb-diagonal-rlim-tower-limit-preservation). -/
theorem diagonalRlimTowerLimitPreservation (l : ℕ) [Fact l.Prime]
    {X S : Scheme.{u}} (f : X ⟶ S)
    [DiagonalTraceLocalizations l X] [DiagonalTraceLocalizations l S]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : S, Invertible (l : S.residueField y)]
    (cS : Chern l (ULift.{u} (Padic l)) S)
    (rS : Restriction l (ULift.{u} (Padic l)) S)
    (aS : Coefficients l (ULift.{u} (Padic l)) S cS rS) :
    PreservesLimit (rS.F.obj (coefficient S (Arings l (ULift.{u} (Padic l)) S)))
        (upperStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) f) ∧
      PreservesLimit (rS.F.obj (lineModule l (ULift.{u} (Padic l)) cS))
        (upperStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) f) := by
  constructor
  · let := coefficient_ab_preserves l f
    let := preservesLimit_of_iso_diagram (upperStar AddCommGrpCat.{u + 1} f)
      aS.coefficientForget.symm
    exact pull_preserves_of_forget l f _
  · let := root_ab_preserves l f
    let := preservesLimit_of_iso_diagram (upperStar AddCommGrpCat.{u + 1} f)
      aS.lineForget.symm
    exact pull_preserves_of_forget l f _

end AlgebraicGeometry.ProEtale.DiagonalTrace
