/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Scalar.TowerScalarSingleCounit
public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Chern.TowerChernPullbackData
public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Class.TowerClassPullback
import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Integral.TowerIntegralCoefficientPullbackExistence
import WeilConjectures.AlgebraicGeometry.SpTowerClasses.TowerOrdinaryScalarAssociation
import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Scalar.TowerScalarCounitNormalization

/-! # Ordinary scalar association for the integral quotient tower
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u a b c d
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures
namespace AlgebraicGeometry.ProEtale.SpTowerClasses

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

attribute [local instance] SheafOfModules.isMonoidal_W_independentCoefficients
  SheafOfModules.monoidalCategory
  SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients
  SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients

-- These two private calculations follow TowerChernScalarUnit.
/-- Ordinary inverse image and balanced scalar association, normalized at the unit
and root modules. The last two equations are in the abelian category of A-systems;
there is no derived scalar/pullback comparison in this statement. -/
theorem tower_chernOrdinaryScalar_pullback
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hX : IsUnit (l : Γ(X, ⊤))) (hY : IsUnit (l : Γ(Y, ⊤)))
    (b : SpTowerShriek.Base l E) (g : SpTowerShriek.Geometry l E b f)
    (cY : Chern l E Y) (cX : Chern l E X)
    (nY : cY.Normalized l E) (nX : cX.Normalized l E)
    (θ₀ : CoefficientPullback l E b f g) (θ₁ : LinePullback l E f g cY cX) :
    ∃ d : IntegralCoefficientPullback l E f cY cX,
    ∃ α : cY.scalar.model.E ⋙ g.pull ≅ d.pull ⋙ cX.scalar.model.E,
    ∃ eY : cY.scalar.model.E.obj (coefficient Y (Rrings l Y)) ⟶
        coefficient Y (Arings l E Y),
    ∃ eX : cX.scalar.model.E.obj (coefficient X (Rrings l X)) ⟶
        coefficient X (Arings l E X),
      (∀ (P : CochainComplex (Systems Y (Rrings l Y)) ℤ),
        CochainComplex.IsKFlatIndependentCoefficients
          (R := WeilConjectures.SemilinearSections.systemRing
            (Scheme.ProEt.topology Y) (fun n ↦ (Rrings l Y).obj (Opposite.op n))
              (fun n ↦ (Rrings l Y).map (homOfLE (Nat.le_succ n)).op)) P →
        (∀ i : ℤ, SheafOfModules.IsFlatOnSite
          (J := WeilConjectures.coefficientSequenceTopology (Scheme.ProEt.topology Y))
          (R := WeilConjectures.SemilinearSections.systemRing
            (Scheme.ProEt.topology Y) (fun n ↦ (Rrings l Y).obj (Opposite.op n))
              (fun n ↦ (Rrings l Y).map (homOfLE (Nat.le_succ n)).op)) (P.X i)) →
        CochainComplex.IsKFlatIndependentCoefficients
          (R := WeilConjectures.SemilinearSections.systemRing
            (Scheme.ProEt.topology X) (fun n ↦ (Rrings l X).obj (Opposite.op n))
              (fun n ↦ (Rrings l X).map (homOfLE (Nat.le_succ n)).op))
          ((d.pull.mapHomologicalComplex (.up ℤ)).obj P)) ∧
      (scalarSingleCounit cY).app (coefficient Y (Rrings l Y)) ≫
          (DerivedCategory.singleFunctor (Systems Y (Arings l E Y)) 0).map eY =
        cY.scalarUnit.hom ∧
      (scalarSingleCounit cX).app (coefficient X (Rrings l X)) ≫
          (DerivedCategory.singleFunctor (Systems X (Arings l E X)) 0).map eX =
        cX.scalarUnit.hom ∧
      α.hom.app (coefficient Y (Rrings l Y)) ≫ cX.scalar.model.E.map d.unitIso.hom ≫ eX =
        g.pull.map eY ≫ θ₀.iso.hom ∧
      α.hom.app cY.rootModule ≫ cX.scalar.model.E.map d.rootIso.hom = θ₁.iso.hom := by
  obtain ⟨d, hk, hflat⟩ := integralCoefficientPullback_exists l E f hX hY cY cX
  let eY := (cY.scalar.ordinaryAdjunction.homEquiv _ _).symm (scalarGenerator l E Y)
  let eX := (cX.scalar.ordinaryAdjunction.homEquiv _ _).symm (scalarGenerator l E X)
  have heY : (cY.scalar.ordinaryAdjunction.homEquiv _ _) eY = scalarGenerator l E Y :=
    Equiv.apply_symm_apply _ _
  have heX : (cX.scalar.ordinaryAdjunction.homEquiv _ _) eX = scalarGenerator l E X :=
    Equiv.apply_symm_apply _ _
  obtain ⟨α, hu, hr⟩ := ordinaryScalarAssociation_exists l E f hX hY b g cY cX nY nX
    θ₀ θ₁ d hk eY eX heY heX
  exact ⟨d, α, eY, eX, hflat, scalarCounitNormalization l E cY nY eY heY,
    scalarCounitNormalization l E cX nX eX heX, hu, hr⟩

end AlgebraicGeometry.ProEtale.SpTowerClasses
