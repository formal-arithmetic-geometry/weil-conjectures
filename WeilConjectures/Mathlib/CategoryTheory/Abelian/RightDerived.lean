/-
Copyright (c) 2026 The Weil Conjectures Project Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.Abelian.RightDerived

/-!
# Acyclic resolutions compute right derived functors

For a left exact additive functor `F : C ⥤ D` between abelian categories, where `C` has
injective resolutions, the right derived functors `F.rightDerived q` may be computed using
any resolution `X → I⁰ → I¹ → ⋯` of `X` by `F`-acyclic objects, i.e. objects `Iⁿ` with
`(F.rightDerived q).obj Iⁿ = 0` for all `q > 0`. This generalises
`InjectiveResolution.isoRightDerivedObj`.

## Main results

* `CategoryTheory.Functor.nonempty_rightDerivedObjIso_homology_of_acyclic`: the acyclicity
  criterion.
-/

@[expose] public section

universe v u

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C] {D : Type*} [Category* D]
  [Abelian C] [HasInjectiveResolutions C] [Abelian D]

/-- **Acyclicity criterion.** Let `F : C ⥤ D` be a left exact additive functor and let
`ι : X → I` be a resolution of `X` (a quasi-isomorphism from `X` placed in degree `0` to a
cochain complex `I` indexed by `ℕ`) by `F`-acyclic objects, i.e. `R^q F (Iⁿ) = 0` for all
`q > 0` and all `n`. Then `R^q F (X) ≅ H^q (F(I))` for all `q`.
(blueprint: `sk-thm-acyclicity`) -/
theorem Functor.nonempty_rightDerivedObjIso_homology_of_acyclic (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] {X : C} (I : CochainComplex C ℕ)
    (ι : (CochainComplex.single₀ C).obj X ⟶ I) [QuasiIso ι]
    (hI : ∀ n q : ℕ, IsZero ((F.rightDerived (q + 1)).obj (I.X n))) (q : ℕ) :
    Nonempty ((F.rightDerived q).obj X ≅
      (HomologicalComplex.homologyFunctor D _ q).obj
        ((F.mapHomologicalComplex _).obj I)) := by
  sorry

end CategoryTheory
