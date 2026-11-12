/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.ThickOriginFiniteModule

/-!
# Short exact sequences of coefficients give distinguished triangles of constant complexes

For a finite coefficient ring `T` and a scheme `Y`, the constant complex functor
`ProEtale.finiteCoefficientConstantFunctor T Y` is the composite of the constant étale sheaf
functor, the inclusion in degree `0`, the derived pullback `ν^*` and the inverse of the derived
comparison. The first functor is exact and the others are triangulated, so a short exact sequence
`0 → M₁ → M₂ → M₃ → 0` of `T`-modules gives a distinguished triangle
`M₁_Y → M₂_Y → M₃_Y → M₁_Y[1]`.

## Main results

- `ProEtale.exists_distinguished_finiteCoefficientConstantFunctor`: the distinguished triangle
  attached to a short exact sequence of `T`-modules.
-/

@[expose] public noncomputable section

universe u

open CategoryTheory Limits Pretriangulated

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

variable (T : Type) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] [DiscreteTopology T]
  [Finite T]

/-- A short exact sequence `0 → M₁ → M₂ → M₃ → 0` of modules over a finite coefficient ring `T`
gives a distinguished triangle `M₁_Y → M₂_Y → M₃_Y → M₁_Y[1]` of constant complexes on `Y`. -/
theorem exists_distinguished_finiteCoefficientConstantFunctor (Y : Scheme.{u})
    {S : ShortComplex (ModuleCat.{u + 1} (ULift.{u + 1} T))} (hS : S.ShortExact) :
    ∃ h, Triangle.mk ((finiteCoefficientConstantFunctor T Y).map S.f)
      ((finiteCoefficientConstantFunctor T Y).map S.g) h ∈ distTriang _ := by
  let _ : (finiteCoefficientDerivedEquivalence Y T).inverse.CommShift ℤ :=
    inferInstanceAs (D((finiteCoefficientModEquivalence Y T).inverse).CommShift ℤ)
  have : (finiteCoefficientDerivedEquivalence Y T).inverse.IsTriangulated :=
    inferInstanceAs (D((finiteCoefficientModEquivalence Y T).inverse).IsTriangulated)
  exact ⟨_, (finiteCoefficientDerivedEquivalence Y T).inverse.map_distinguished _
    (D(ν^*(Y)[ModuleCat.{u + 1} (ULift.{u + 1} T)]).map_distinguished _
      (hS.map_of_exact (constantSheaf Y.smallEtaleTopology
        (ModuleCat.{u + 1} (ULift.{u + 1} T)))).singleTriangle_distinguished)⟩

end AlgebraicGeometry.ProEtale
