/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import WeilConjectures.AlgebraicGeometry.Curve.DenseOpenHighCohomologyHigh
import WeilConjectures.AlgebraicGeometry.Curve.DenseOpenHighCohomologyPullback

/-! # Higher cohomology across a dense open -/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry.Etale

namespace AlgebraicGeometry.IsCurve

/-- The counit from extension by zero induces bijections in degrees above one,
including degree two after restriction to any open immersion.
Source: Stacks Project, Tag 0GJA, proof, the higher-degree isomorphisms and remark (d). -/
theorem dense_open_high_cohomology (Λ : Type (u + 1)) [CommRing Λ]
    {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsCurve f]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (U : X.Opens) (hU : Dense (U : Set X)) :
    let ε := (sheafCompose X.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).map
        ((openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) U.ι).counit.app F)
    (∀ q : ℕ, 1 < q → Function.Bijective (Sheaf.H.map ε q)) ∧
      (∀ {W : Scheme.{u}} (a : W ⟶ X) [IsOpenImmersion a],
        Function.Bijective
          (Sheaf.H.map (((a)^*[AddCommGrpCat.{u + 1}]).map ε) 2)) := by
  dsimp
  exact ⟨dense_open_high_cohomology_high Λ f F U hU,
    dense_open_high_cohomology_pullback Λ f F U hU⟩

end AlgebraicGeometry.IsCurve
