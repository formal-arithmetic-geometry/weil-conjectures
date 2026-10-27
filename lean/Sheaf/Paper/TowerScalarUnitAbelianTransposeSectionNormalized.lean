/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A9
-/
module

public import Sheaf.Paper.TowerRestrictedScalarAdjunction
public import Sheaf.Paper.TowerClassPullback

/-! # Normalized coefficient-unit transpose section calculation -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures
namespace AlgebraicGeometry.ProEtale.SpTowerClasses

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The canonical ordinary scalar map whose adjunct is `scalarGenerator`. -/
noncomputable def canonicalScalarUnit {T : Scheme.{u}} (c : Chern l E T) :
    c.scalar.model.E.obj (coefficient T (Rrings l T)) ⟶
      coefficient T (Arings l E T) :=
  (c.scalar.ordinaryAdjunction.homEquiv _ _).symm (scalarGenerator l E T)

/--
The sectionwise transpose identity in the normalized case, where the two scalar
maps are the canonical adjuncts of `scalarGenerator`.  This is the ordinary
coefficient-unit calculation: evaluate the adjunctions at one level and one
chart, use the geometric naturality and the `CoefficientPullback.normalization`
and `IntegralCoefficientPullback.unit_normalization` equations on constant
integer sections, then extend by the local surjectivity of the constant integer
sheaf and separatedness.  Empty charts and zero rings are included.

Source: blueprint classes proof (2), ordinary coefficient-unit normalization;
Stacks 03EL. (blueprint: lem-sp-tower-scalar-unit-abelian-transpose-section)
-/
theorem scalarUnit_abelianTranspose_section_normalized
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
    (θ₀ : CoefficientPullback l E b f g)
    (n : ℕᵒᵖ) (U : Y.ProEtᵒᵖ)
    (x : ((cY.reduction.forget.F.obj (coefficient Y (Rrings l Y))).obj n).obj.obj U) :
    (AddCommGrpCat.Hom.hom
      (((cY.reduction.forget.F.map
        (((cY.scalar.ordinaryAdjunction.comp g.ordinaryAdjunction).homEquiv _ _)
          (g.pull.map (canonicalScalarUnit l E cY) ≫ θ₀.iso.hom)) ≫
        χ.hom.app (coefficient X (Arings l E X))).app n).hom.app U)) x =
      (AddCommGrpCat.Hom.hom
        (((((abAdjunction f).homEquiv _ _)
          (d.forgetIso.hom.app (coefficient Y (Rrings l Y)) ≫
            cX.reduction.forget.F.map
              ((cX.scalar.ordinaryAdjunction.homEquiv _ _)
                (cX.scalar.model.E.map d.unitIso.hom ≫
              canonicalScalarUnit l E cX)))).app n).hom.app U)) x := by
  sorry

end AlgebraicGeometry.ProEtale.SpTowerClasses
