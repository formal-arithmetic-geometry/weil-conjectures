/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.DeligneLaumon.PoweredGeometricPullback

/-! # The carrier comparison for powered geometric pullback

Source: the definition of powered pullback in `sk-i-dl-general-real`.
(blueprint: def-zl-powered-pullback-carrier).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Limits Endofunctor
open scoped AlgebraicGeometry.ProEtale
namespace AlgebraicGeometry.WeilSheaf

variable {k₀ k₁ : Type u} [Field k₀] [Finite k₀] [Field k₁] [Finite k₁]
  {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)] [Fact (ringChar k₁ ≠ l)]
  {X C : Scheme.{u}} [X.Over (Spec (.of k₀))] [C.Over (Spec (.of k₁))]
  (v : (C ↘ Spec (.of k₁)).geometricFiber ⟶ (X ↘ Spec (.of k₀)).geometricFiber)
  (r : ℕ)
  (hv : (C ↘ Spec (.of k₁)).geometricGaloisFrobenius.hom ≫ v =
    v ≫ ((X ↘ Spec (.of k₀)).geometricGaloisFrobenius ^ r).hom)

/-- Powered pullback has the ordinary pullback as its carrier functor.
Source: the explicit `powFunctor` and `mapOfNatIso` constructions.
(blueprint: def-zl-powered-pullback-carrier). -/
noncomputable def poweredPullbackAllCarrierIso :
    poweredGeometricPullbackAll (l := l) v r hv ⋙
        IsoAlgebra.forget (frobeniusPullback k₁ l C) ≅
      IsoAlgebra.forget (frobeniusPullback k₀ l X) ⋙ (v)^*ᵃ[l] := by
  unfold poweredGeometricPullbackAll ProEtaleWeilSheaf.powFunctor
  exact Iso.refl _

/-- Forgetting constructibility commutes with powered pullback.
Source: restriction to the full subcategory of constructible carriers.
(blueprint: def-zl-powered-pullback-carrier). -/
noncomputable def poweredPullbackInclusionIso :
    poweredGeometricPullback (l := l) v r hv ⋙ (objectProperty k₁ l C).ι ≅
      (objectProperty k₀ l X).ι ⋙ poweredGeometricPullbackAll v r hv := by
  unfold poweredGeometricPullback
  exact ObjectProperty.liftFullSubcategoryCompιIso
    (objectProperty k₀ l X) (objectProperty k₁ l C) (poweredGeometricPullbackAll v r hv)
    (fun (G : ProEtaleWeilSheaf k₀ l X)
      (h : ProEtale.IsAdicConstructibleSheaf G.carrier) ↦ by
      change ProEtale.IsAdicConstructibleSheaf
        ((poweredGeometricPullbackAll v r hv).obj G).carrier
      rw [poweredGeometricPullbackAll_obj_carrier]
      exact h.upperStar v)

attribute [irreducible] poweredPullbackAllCarrierIso poweredPullbackInclusionIso

end AlgebraicGeometry.WeilSheaf
