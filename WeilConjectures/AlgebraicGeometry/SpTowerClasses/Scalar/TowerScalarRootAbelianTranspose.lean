/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.TowerRestrictedScalarAdjunction
public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Class.TowerClassPullback
import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Scalar.TowerScalarRootAbelianTransposeComponent

/-! # The abelian transpose of the ordinary root comparison
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures
namespace AlgebraicGeometry.ProEtale.SpTowerClasses

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- Kernel restriction and the normalized finite line have the same abelian transpose.
Neither the existence nor the invertibility of scalar association is asserted here.

Source: Stacks 03EL. -/
theorem scalarRoot_abelianTranspose
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (b : SpTowerShriek.Base l E) (g : SpTowerShriek.Geometry l E b f)
    (cY : Chern l E Y) (cX : Chern l E X)
    (d : IntegralCoefficientPullback l E f cY cX)
    (χ : (g.push ⋙ SemilinearSections.res.{u + 1, u, u + 1}
        (coefficientSystemMap l E Y)) ⋙ cY.reduction.forget.F ≅
      (SemilinearSections.res.{u + 1, u, u + 1}
        (coefficientSystemMap l E X) ⋙ cX.reduction.forget.F) ⋙ abPush f)
    (hχ : ∀ (N : Systems X (Arings l E X)) (n : ℕ) (U : Y.ProEtᵒᵖ)
      (x : (((cY.reduction.forget.F.obj
        ((SemilinearSections.res.{u + 1, u, u + 1}
          (coefficientSystemMap l E Y)).obj (g.push.obj N))).obj (op n)).obj.obj U)),
      HEq ((((χ.hom.app N).app (op n)).hom.app U) x) x)
    (hk : ∀ n : ℕ, d.kummer.τ₂.app (op n) = (unitsPull f).app (op n))
    (θ₁ : LinePullback l E f g cY cX) :
    cY.reduction.forget.F.map
        (((cY.scalar.ordinaryAdjunction.comp g.ordinaryAdjunction).homEquiv _ _)
          θ₁.iso.hom) ≫ χ.hom.app (lineModule l E cX) =
      ((abAdjunction f).homEquiv _ _)
        (d.forgetIso.hom.app cY.rootModule ≫ cX.reduction.forget.F.map
          ((cX.scalar.ordinaryAdjunction.homEquiv _ _)
            (cX.scalar.model.E.map d.rootIso.hom))) := by
  ext n U x
  exact scalarRoot_abelianTranspose_component l E f b g cY cX d χ hχ hk θ₁ n U x

end AlgebraicGeometry.ProEtale.SpTowerClasses
