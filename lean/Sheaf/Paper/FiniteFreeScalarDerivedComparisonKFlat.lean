/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Sheaf.Paper.IntegralFiniteScalarModelDefinitions

/-! K-flatness part of the finite-free scalar comparison.
(blueprint: lem-sfb-finite-free-scalar-derived-comparison-flatness)
-/
@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.IntegralFiniteScalar
open CondensedRing

/-- The sectionwise image of the pulled-back finite-free complex is K-flat.

Source: the finite-free mono-cokernel theorem after point pullback and the exact
internal-to-sectionwise equivalence.  The theorem's independent-coefficient clause
is transported back along the fixed equivalence, giving the displayed complex.
-/
theorem finiteFreeScalarDerivedComparison_kflat
    (D : ScalarSixPullbackData.{u}) {Λ Λ' : ScalarSixRing.{u}}
    (a : Λ ⟶ Λ') (S : ShortComplex (PointModules Λ))
    (t : S.X₃ ≅ (Mod.comap a.hom.hom).obj (Mod.regular Λ'.X))
    (hS : S.ShortExact) (r : ℕ)
    (e₁ : S.X₁ ≅ biproduct (fun _ : Fin r ↦ Mod.regular Λ.X))
    (e₂ : S.X₂ ≅ biproduct (fun _ : Fin r ↦ Mod.regular Λ.X))
    (Z : Scheme.{u}) :
    CochainComplex.IsKFlatIndependentCoefficients
      (((ModuleRingedComparison.equivalence Λ.X Z).functor.mapHomologicalComplex
        (.up ℤ)).obj (complex Λ S Z)) := by
  sorry

end AlgebraicGeometry.ProEtale.IntegralFiniteScalar
