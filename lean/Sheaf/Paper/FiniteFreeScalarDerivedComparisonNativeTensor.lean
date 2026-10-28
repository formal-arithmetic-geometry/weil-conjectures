/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Sheaf.Paper.IntegralFiniteScalarModelDefinitions

/-! Native derived tensor consequence for the finite-free scalar model.
(blueprint: lem-sfb-finite-free-scalar-derived-comparison-flatness)
-/
@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.IntegralFiniteScalar
open CondensedRing

/-- K-flatness gives the native derived tensor comparison isomorphism.

Source: the normalized sectionwise native-tensor theorem and transport across the
fixed internal/module equivalence.  Resolve the two factors by the K-flat complex;
the normalized total-tensor comparison is an isomorphism and localization preserves
it, yielding the displayed `DerivedCategory.Q` multiplication map.
-/
theorem finiteFreeScalarDerivedComparison_nativeTensor
    (D : ScalarSixPullbackData.{u}) {Λ Λ' : ScalarSixRing.{u}}
    (a : Λ ⟶ Λ') (S : ShortComplex (PointModules Λ))
    (t : S.X₃ ≅ (Mod.comap a.hom.hom).obj (Mod.regular Λ'.X))
    (hS : S.ShortExact) (r : ℕ)
    (e₁ : S.X₁ ≅ biproduct (fun _ : Fin r ↦ Mod.regular Λ.X))
    (e₂ : S.X₂ ≅ biproduct (fun _ : Fin r ↦ Mod.regular Λ.X))
    (Z : Scheme.{u})
    (hK : CochainComplex.IsKFlatIndependentCoefficients
      (((ModuleRingedComparison.equivalence Λ.X Z).functor.mapHomologicalComplex
        (.up ℤ)).obj (complex Λ S Z))) :
    ∀ C : CochainComplex (ModuleRingedComparison.internalModules Λ.X Z) ℤ,
      IsIso (Functor.LaxMonoidal.μ DerivedCategory.Q (complex Λ S Z) C) := by
  sorry

end AlgebraicGeometry.ProEtale.IntegralFiniteScalar
