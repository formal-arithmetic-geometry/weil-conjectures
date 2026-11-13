/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.Single
import WeilConjectures.AlgebraicGeometry.AffineFiniteFreePerfectCore
import WeilConjectures.AlgebraicGeometry.AffineFiniteFreePerfectComparison

/-!
# Local strictly perfect models from bounded finite free resolutions

Source: Stacks Project, Tag 068C, finite free resolution argument, and Tags 08C4, 08CM.
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A bounded finite free algebraic chain complex resolving a sheaf on an affine
open supplies a strictly perfect model for its derived restriction to that open.
Source: Stacks Project, Tag 068C, and Definitions 08C4, 08CM. -/
theorem exists_affine_finite_free_perfect_model {Y : Scheme.{u}}
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ U : Y.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over U))]
    (U : Y.Opens) (hU : IsAffineOpen U)
    (M : SheafOfModules.{u} (moduleRings Y.toRingedSpace))
    (K : ChainComplex (ModuleCat.{u} (Γ(Y, U) : Type u)) ℕ) (r : ℕ)
    (hfree : ∀ n, Module.Free (Γ(Y, U) : Type u) (K.X n))
    (hfinite : ∀ n, Module.Finite (Γ(Y, U) : Type u) (K.X n))
    (hzero : ∀ n, r < n → IsZero (K.X n))
    (q : ((tilde.functor Γ(Y, U) ⋙
          Scheme.Modules.restrictFunctor hU.isoSpec.hom).mapHomologicalComplex
            (ComplexShape.down ℕ)).obj K ⟶
        (ChainComplex.single₀ U.toScheme.Modules).obj
          ((Scheme.Modules.restrictFunctor U.ι).obj M))
    [QuasiIso q] :
    ∃ L : CochainComplex
        (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over U)) ℤ,
      Scheme.IsStrictlyPerfect Y U L ∧
      Nonempty ((SheafOfModules.overFunctor.{u}
        (moduleRings Y.toRingedSpace) U).mapDerivedCategory.obj
          ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj M) ≅
              DerivedCategory.Q.obj L) := by
  refine ⟨affineFiniteFreeModelComplex U hU K, ?_, ?_⟩
  · exact affine_finite_free_perfect_core U hU K r hfree hfinite hzero
  · exact affine_finite_free_perfect_comparison U hU M K q

end AlgebraicGeometry
