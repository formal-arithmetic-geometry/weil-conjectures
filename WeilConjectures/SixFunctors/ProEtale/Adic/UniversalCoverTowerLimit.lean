/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.ContinuousMapAdd
public import WeilConjectures.SixFunctors.ProEtale.Comparison.UniversalCoverConstant
public import WeilConjectures.CategoryTheory.Sites.ConstantSheafCompose

/-!
# Limits of towers of finite locally constant sheaves on the universal cover

- `AlgebraicGeometry.ProEtale.constantSheafTowerCompForget₂IsoAdd`: the abelian tower underlying
  a tower of constant pro-étale sheaves of modules `n ↦ (Mₙ)_X` is `n ↦ C(-, Qₙ)`, for discrete
  groups `Qₙ ≅ Mₙ` compatible with the transitions; hence its limit is `C(-, lim Qₙ)`
  (`AlgebraicGeometry.ProEtale.exists_isLimit_continuousMapAddSheaf_of_iso`).
- `AlgebraicGeometry.Scheme.UniversalCovers.exists_isLimit_towerComparisonUpperStar`: for a tower
  `H` of finite locally constant étale sheaves on `Y`, the abelian tower underlying `p^* ν^* Hₙ`
  on the universal cover `Ỹ_y` has limit `C(-, lim_n (Hₙ)_y)`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.ProEtale

open Scheme

section Bridge

variable (X : Scheme.{u}) {Λ : Type (u + 1)} [Ring Λ] {Qs : ℕ → Type}
  [∀ n, TopologicalSpace (Qs n)] [∀ n, AddCommGroup (Qs n)] [∀ n, IsTopologicalAddGroup (Qs n)]
  [∀ n, DiscreteTopology (Qs n)] (τ : ∀ n, Qs (n + 1) →+ Qs n)
  (M : ℕᵒᵖ ⥤ ModuleCat.{u + 1} Λ)
  (e : ∀ n, M.obj (op n) ≃+ ULift.{u + 1} (Qs n))
  (he : ∀ n x, e n (M.map (homOfLE (n.le_add_right 1)).op x) = ULift.up (τ n (e (n + 1) x).down))

end Bridge

end AlgebraicGeometry.ProEtale
