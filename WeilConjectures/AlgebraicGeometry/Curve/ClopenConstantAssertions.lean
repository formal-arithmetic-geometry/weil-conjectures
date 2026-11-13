/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Curve.Assertions
import WeilConjectures.AlgebraicGeometry.Curve.ClopenConstantAssertionsFirst
import WeilConjectures.AlgebraicGeometry.Curve.ClopenConstantAssertionsLast
import WeilConjectures.AlgebraicGeometry.EtaleCohomologyPullbackFunctorial
import WeilConjectures.AlgebraicGeometry.EtaleSheafClopenProduct
import WeilConjectures.AlgebraicGeometry.FiniteCoproductCohomologyAssembly
import WeilConjectures.AlgebraicGeometry.Sites.CohomologyClopen
import WeilConjectures.ConstructibleSheaf.Pullback

/-! # Assembling constant-coefficient assertions over a finite clopen partition -/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.IsCurve

/-- Constant-coefficient curve assertions assemble over a finite clopen partition. -/
theorem assertions_constant_of_isClopen (Λ : Type (u + 1)) [CommRing Λ]
    {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsCurve f] (M : ModuleCat.{u + 1} Λ)
    {ι : Type u} [Finite ι] (U : ι → X.Opens)
    (hU : ∀ i, IsClosed (U i : Set X))
    (hdisj : Pairwise (fun i j ↦ Disjoint (U i : Set X) (U j)))
    (hcov : ∀ x : X, ∃ i, x ∈ U i)
    (H : ∀ i, Assertions Λ ((U i).ι ≫ f)
      ((constantSheaf (U i).toScheme.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)) :
    Assertions Λ f ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M) := by
  rcases clopen_first_four Λ f M U hU hdisj hcov H with ⟨h1, h2, h3, h4⟩
  rcases clopen_last_four Λ f M U hU hdisj hcov H with ⟨h5, h6, h7, h8⟩
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩

end AlgebraicGeometry.IsCurve
