/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.TowerRestrictedScalarAdjunction
public import Sheaf.Paper.TowerClassPullback

/-! # Core finite-level root normalization comparison -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures
namespace AlgebraicGeometry.ProEtale.SpTowerClasses

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The scalar-unit/geometric-transpose value at one finite level and chart. -/
def scalarRootCoreSource
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (b : SpTowerShriek.Base l E) (g : SpTowerShriek.Geometry l E b f)
    (cY : Chern l E Y) (cX : Chern l E X)
    (θ₁ : LinePullback l E f g cY cX)
    (n : ℕᵒᵖ) (U : Y.ProEtᵒᵖ)
    (x : (((cY.reduction.forget.F.obj cY.rootModule).obj n).obj.obj U)) :=
  (((cY.reduction.forget.F.map
    ((cY.scalar.ordinaryAdjunction.unit.app cY.rootModule) ≫
      (SemilinearSections.res.{u + 1, u, u + 1}
        (coefficientSystemMap l E Y)).map
        (g.ordinaryAdjunction.homEquiv _ _ θ₁.iso.hom))).app n).hom.app U) x

/-- The abelian-transpose value at one finite level and chart. -/
def scalarRootCoreRight
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (cY : Chern l E Y) (cX : Chern l E X)
    (d : IntegralCoefficientPullback l E f cY cX)
    (n : ℕᵒᵖ) (U : Y.ProEtᵒᵖ)
    (x : (((cY.reduction.forget.F.obj cY.rootModule).obj n).obj.obj U)) :=
  (((((abAdjunction f).homEquiv _ _)
    (d.forgetIso.hom.app cY.rootModule ≫
      cX.reduction.forget.F.map
        ((cX.scalar.ordinaryAdjunction.homEquiv _ _)
          (cX.scalar.model.E.map d.rootIso.hom)))).app n).hom.app U) x


/--
The finite root normalization comparison after expanding both scalar adjunction
transposes to their units.  This is the χ-free core of the component calculation.

Source: blueprint latest, classes proof (2), finite-level evaluation of the
abelian transpose before assembling the tower map; Stacks 03EL.
(blueprint: lem-sp-tower-scalar-root-abelian-transpose-component-core)

Proof: evaluate the scalar unit as the sheafified pure tensor, evaluate the
ordinary geometric transpose on that tensor, and use the normalized line
comparison.  The Kummer boundary square, `hk`, and `d.kummer_roots` identify
its root with `restrictRoot`; `LinePullback.normalization` then gives the
same finite Tate tensor as the abelian transpose after `d.rootIso`.
-/
theorem scalarRoot_abelianTranspose_core
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (b : SpTowerShriek.Base l E) (g : SpTowerShriek.Geometry l E b f)
    (cY : Chern l E Y) (cX : Chern l E X)
    (d : IntegralCoefficientPullback l E f cY cX)
    (hk : ∀ n : ℕ, d.kummer.τ₂.app (op n) = (unitsPull f).app (op n))
    (θ₁ : LinePullback l E f g cY cX)
    (n : ℕᵒᵖ) (U : Y.ProEtᵒᵖ)
    (x : (((cY.reduction.forget.F.obj cY.rootModule).obj n).obj.obj U)) :
    HEq (scalarRootCoreSource l E f b g cY cX θ₁ n U x)
      (scalarRootCoreRight l E f cY cX d n U x) := by
  sorry

end AlgebraicGeometry.ProEtale.SpTowerClasses
