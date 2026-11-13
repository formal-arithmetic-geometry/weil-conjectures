/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.RoosCohomologyMaps
import WeilConjectures.AlgebraicGeometry.RoosCohomologyNaturality

/-! # The natural cohomology sequence of a strict Roos complex

For a tower of complexes `K`, the cohomology of its Roos complex sits in a natural short exact
sequence between the cokernel term of the cohomology tower in degree `q - 1` and the limit of
the cohomology tower in degree `q`.
-/

@[expose] public section

set_option autoImplicit false

universe a b

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.ProEt

/-- The natural short exact sequence `0 → lim¹ H^{q-1} → H^q(Roos K) → lim H^q → 0` coming
from the long exact sequence of `Cone(1 - T)[-1]`, natural in the tower `K`. -/
theorem roos_cohomology_sequence {A : Type a} [Category.{b} A] [Abelian A]
    [HasCountableLimits A] [HasExactLimitsOfShape (Discrete ℕ) A] :
    ∀ q : ℤ,
        ∃ (a : ∀ K : ℕᵒᵖ ⥤ CochainComplex A ℤ,
            milnorTowerCokernel (milnorCohomologyTower K (q - 1)) ⟶
              (WeilConjectures.integralOperationsRoos K).homology q)
          (b : ∀ K : ℕᵒᵖ ⥤ CochainComplex A ℤ,
            (WeilConjectures.integralOperationsRoos K).homology q ⟶
              limit (milnorCohomologyTower K q)),
          (∀ K : ℕᵒᵖ ⥤ CochainComplex A ℤ,
            ∃ h : a K ≫ b K = 0, (ShortComplex.mk (a K) (b K) h).ShortExact) ∧
          (∀ (K L : ℕᵒᵖ ⥤ CochainComplex A ℤ) (f : K ⟶ L),
            milnorTowerCokernelMap
                (Functor.whiskerRight f
                  (HomologicalComplex.homologyFunctor A
                    (ComplexShape.up ℤ) (q - 1))) ≫ a L =
              a K ≫ HomologicalComplex.homologyMap
                (WeilConjectures.integralOperationsRoosMap f) q ∧
            HomologicalComplex.homologyMap
                (WeilConjectures.integralOperationsRoosMap f) q ≫ b L =
              b K ≫ limMap (Functor.whiskerRight f
                (HomologicalComplex.homologyFunctor
                  A (ComplexShape.up ℤ) q))) := by
  intro q
  refine ⟨fun K ↦ milnorInclusion K q, fun K ↦ milnorProjection K q,
    fun K ↦ milnor_shortExact K q, ?_⟩
  intro K L f
  exact roos_cohomology_naturality q f

end AlgebraicGeometry.Scheme.ProEt
