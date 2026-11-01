/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Realization.DiagonalRealizationPullback
public import Mathlib.CategoryTheory.Adjunction.Mates
import all WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafChangeAdjunctionSupplement
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.DiagonalRlimForgetUnit

/-! # Invertibility of the completed scalar inverse-image mate -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale.DiagonalTrace

set_option maxHeartbeats 1000000 in
-- Elaborating the full unit and mate comparisons needs a larger heartbeat budget.
/-- The inverse-image mate of a sectionwise identity completed direct-image square
is invertible.

Source: blueprint coefficient proof (3), exact completed scalar restriction.
At each module, apply the abelian inverse-image adjunction to the two underlying
unit maps. The fixed-scalar unit has invertible abelian adjunct by the normalized
forgetting comparison. The completed module unit has invertible abelian adjunct
by the ring-sheaf inverse-image unit comparison. The mate unit equation says
that the underlying mate carries the first unit to the second, since the
specified direct-image comparison is the identity on sections. Naturality of
the abelian adjunction identifies the mate with the quotient of those two
invertible adjuncts. Scalar forgetting reflects isomorphisms. Finally the
componentwise inverses assemble by naturality.
(blueprint: new-sfb-diagonal-rlim-completed-scalar-mate). -/
theorem diagonalRlimCompletedScalarMate (l : ℕ) [Fact l.Prime]
    {X S : Scheme.{u}} (f : X ⟶ S)
    (d : Scheme.proEtaleRingModuleDirectImage f
        (Scheme.purTwistZlCompletion S l) (Scheme.purTwistZlCompletion X l)
        (asIso (diagonalCompletedCoefficientMap l f)) ⋙ diagonalCompletedRestriction l S ≅
      diagonalCompletedRestriction l X ⋙
        lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) f)
    (hd : ∀ (M : DiagonalCompleted l X) (U : S.ProEtᵒᵖ)
        (x : ((Scheme.proEtaleRingModuleDirectImage f
          (Scheme.purTwistZlCompletion S l) (Scheme.purTwistZlCompletion X l)
          (asIso (diagonalCompletedCoefficientMap l f)) ⋙
          diagonalCompletedRestriction l S).obj M).obj.obj U),
      HEq ((d.hom.app M).hom.app U x) x) :
    IsIso (((mateEquiv (Scheme.proEtaleRingModuleAdjunction f
        (Scheme.purTwistZlCompletion S l) (Scheme.purTwistZlCompletion X l)
        (asIso (diagonalCompletedCoefficientMap l f)))
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) f)).symm
      (TwoSquare.mk _ _ _ _ d.hom)).natTrans) := by
  let ar := Scheme.proEtaleRingModuleAdjunction f
    (Scheme.purTwistZlCompletion S l) (Scheme.purTwistZlCompletion X l)
    (asIso (diagonalCompletedCoefficientMap l f))
  let am := upperStarLowerStarAdjunction (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) f
  let aa := upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f
  let FS := diagonalForget l S
  let FX := diagonalForget l X
  let RS := diagonalCompletedRestriction l S
  let δ := ((mateEquiv ar am).symm (TwoSquare.mk _ _ _ _ d.hom)).natTrans
  have hd' (M : DiagonalCompleted l X) : FS.map (d.hom.app M) = 𝟙 _ := by
    ext U x
    exact eq_of_heq (hd M U x)
  have hi (M : DiagonalCompleted l S) : IsIso (δ.app M) := by
    let : FX.ReflectsIsomorphisms := by
      dsimp [FX, diagonalForget]
      infer_instance
    apply (isIso_iff_of_reflects_iso (δ.app M) FX).mp
    let g := FS.map (am.unit.app (RS.obj M))
    let h := (SheafOfModules.toSheaf
      (Scheme.purTwistRing S (Scheme.purTwistZlCompletion S l))).map (ar.unit.app M)
    let Y := FX.obj
      ((upperStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) f).obj (RS.obj M))
    let Z := (SheafOfModules.toSheaf
      (Scheme.purTwistRing X (Scheme.purTwistZlCompletion X l))).obj
        ((DiagonalCoefficients.diagonalRealizationPull l f).obj M)
    let k : Y ⟶ Z := FX.map (δ.app M)
    change IsIso k
    have hg : IsIso ((aa.homEquiv (FS.obj (RS.obj M)) Y).symm g) :=
      diagonalRlimForgetUnit l f (RS.obj M)
    have hh : IsIso ((aa.homEquiv (FS.obj (RS.obj M)) Z).symm h) :=
      Scheme.ringUnitComparison f (Scheme.purTwistZlCompletion S l)
        (Scheme.purTwistZlCompletion X l) (asIso (diagonalCompletedCoefficientMap l f)) ar M
    have hu := unit_mateEquiv_symm ar am (TwoSquare.mk _ _ _ _ d.hom) M
    have huv := congrArg FS.map hu
    simp only [CategoryTheory.Functor.map_comp, hd'] at huv
    have hk : g ≫ (lowerStar AddCommGrpCat.{u + 1} f).map k = h := by
      exact huv.symm
    exact isoOfAdjunct aa (X := FS.obj (RS.obj M)) (Y := Y) (Z := Z) g h k hg hh hk
  let : ∀ M, IsIso (δ.app M) := hi
  exact NatIso.isIso_of_isIso_app δ

end AlgebraicGeometry.ProEtale.DiagonalTrace
