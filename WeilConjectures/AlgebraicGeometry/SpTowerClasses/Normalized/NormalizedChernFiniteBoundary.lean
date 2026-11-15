/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Class.TowerClassFinite
import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Scalar.TowerScalarFiniteBoundary
import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Integral.TowerIntegralChernNormalization
import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Finite.TowerFiniteChernAssembly

/-! # Finite evaluation of an already normalized Chern construction -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe u u₁ v₁ u₂ v₂ w₁ w₂
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.SpTowerClasses

/-- Normalization of the three adjunction comparisons fixes every finite Chern arrow. -/
theorem finiteChernNormalization_of_normalized (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {T : Scheme.{u}} (c : Chern l E T) (hc : c.Normalized l E) :
    FiniteChernNormalization l E c := by
  apply finiteChernNormalization_of_arrowComparisons l E c
  · intro L
    exact integralArrow_of_normalized l
      (Rrings l T) (Arings l E T) (coefficientSystemMap l E T) c
      (scalarGenerator l E T) hc (lineBundleClass T L)
  · intro f n
    exact scalarFiniteBoundary l E c hc.2.2 f n

end AlgebraicGeometry.ProEtale.SpTowerClasses

attribute [instance high] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
