/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PurityIntegralTower.CondensedTateIntegralTowerData
import WeilConjectures.CategoryTheory.Sites.SheafComposeMonoidalPresheaf

/-! Ordinary semilinear root tensor transitions.

Source: smooth-purity transport, normalized Tate tower, Step 4.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open CategoryTheory.MonoidalCategory
open scoped TensorProduct
open AlgebraicGeometry.Etale.FiniteSmoothPurity
namespace AlgebraicGeometry.Scheme.PurityIntegralTower

variable {A B : Type (u + 1)} [CommRing A] [CommRing B]

private theorem balancingUnitGenerator (R : Type (u + 1)) [CommRing R]
    (X : Scheme.{u}) :
    Functor.LaxMonoidal.ε (sheafToPresheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)) =
      toSheafify X.smallEtaleTopology
        ((Functor.const X.Etaleᵒᵖ).obj (ModuleCat.of R R)) := by
  simp only [Adjunction.rightAdjointLaxMonoidal_ε, Adjunction.homEquiv_unit]
  change _ ≫ (sheafToPresheaf _ _).map (𝟙 _) = _
  simp
  rfl

private theorem balancingRestrictionUnit (φ : A →+* B) (X : Scheme.{u})
    (U : X.Etaleᵒᵖ) (a : A) :
    (Functor.LaxMonoidal.ε (Sheaf.restrictScalars X.smallEtaleTopology φ)).hom.app U
      ((toSheafify X.smallEtaleTopology
        ((Functor.const X.Etaleᵒᵖ).obj (ModuleCat.of A A))).app U a) =
    (toSheafify X.smallEtaleTopology
      ((Functor.const X.Etaleᵒᵖ).obj (ModuleCat.of B B))).app U (φ a) := by
  have h := congrArg (fun t ↦ t.app U)
    (Sheaf.ε_sheafToPresheaf_comp_map_ε_sheafCompose
      X.smallEtaleTopology (ModuleCat.restrictScalars φ))
  rw [balancingUnitGenerator, balancingUnitGenerator] at h
  have hh := ConcreteCategory.congr_hom h a
  change (Functor.LaxMonoidal.ε
    (Sheaf.restrictScalars X.smallEtaleTopology φ)).hom.app U
      ((toSheafify X.smallEtaleTopology
        ((Functor.const X.Etaleᵒᵖ).obj (ModuleCat.of A A))).app U a) =
      (toSheafify X.smallEtaleTopology
        ((Functor.const X.Etaleᵒᵖ).obj (ModuleCat.of B B))).app U
          (Functor.LaxMonoidal.ε (ModuleCat.restrictScalars φ) a) at hh
  simpa only [ModuleCat.restrictScalars_η] using hh

private theorem balancingTensorGenerator (φ : A →+* B) (X : Scheme.{u})
    (M N : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)) (U : X.Etaleᵒᵖ)
    (x : M.obj.obj U) (y : N.obj.obj U) :
    (Functor.LaxMonoidal.μ (Sheaf.restrictScalars X.smallEtaleTopology φ) M N).hom.app U
      ((Functor.LaxMonoidal.μ (sheafToPresheaf X.smallEtaleTopology
        (ModuleCat.{u + 1} A)) _ _).app U (x ⊗ₜ[A] y)) =
    (Functor.LaxMonoidal.μ (sheafToPresheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} B)) M N).app U (x ⊗ₜ[B] y) := by
  have h := congrArg (fun t ↦ t.app U)
    (Sheaf.μ_sheafToPresheaf_comp_map_μ_sheafCompose
      X.smallEtaleTopology (ModuleCat.restrictScalars φ) M N)
  let x' : ((ModuleCat.restrictScalars φ).obj (M.obj.obj U)) := x
  let y' : ((ModuleCat.restrictScalars φ).obj (N.obj.obj U)) := y
  have hh := ConcreteCategory.congr_hom h (x' ⊗ₜ[A] y')
  change (Functor.LaxMonoidal.μ
    (Sheaf.restrictScalars X.smallEtaleTopology φ) M N).hom.app U
      ((Functor.LaxMonoidal.μ (sheafToPresheaf X.smallEtaleTopology
        (ModuleCat.{u + 1} A)) _ _).app U (x' ⊗ₜ[A] y')) =
    (Functor.LaxMonoidal.μ (sheafToPresheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} B)) M N).app U
      (Functor.LaxMonoidal.μ (ModuleCat.restrictScalars φ)
        (M.obj.obj U) (N.obj.obj U) (x' ⊗ₜ[A] y')) at hh
  simpa only [ModuleCat.restrictScalars_μ_tmul] using hh

private theorem balancingTensorMap (R : Type (u + 1)) [CommRing R] (X : Scheme.{u})
    {M N M' N' : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)}
    (f : M ⟶ M') (g : N ⟶ N') (U : X.Etaleᵒᵖ)
    (x : M.obj.obj U) (y : N.obj.obj U) :
    (f ⊗ₘ g).hom.app U
      ((Functor.LaxMonoidal.μ (sheafToPresheaf _ _) M N).app U (x ⊗ₜ[R] y)) =
    (Functor.LaxMonoidal.μ (sheafToPresheaf _ _) M' N').app U
      (f.hom.app U x ⊗ₜ[R] g.hom.app U y) := by
  have h := congrArg (fun t ↦ t.app U)
    (Functor.LaxMonoidal.μ_natural (F := sheafToPresheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} R)) f g)
  exact (ConcreteCategory.congr_hom h (x ⊗ₜ[R] y)).symm

/-- Ordered ordinary semilinear root tensors, with scalar unit at zero.
Source: normalized Tate tower, Step 4.
(blueprint: lem-pur-tate-tensor-ordinary-transition) -/
def finiteTateEtaleTransition
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    {phi : A →+* B} {N M : ℕ} {hA : (N : A) = 0} {hB : (M : B) = 0}
    {T : Scheme.{u}} (r : CoefficientLineComparison phi N M hA hB T) :
    ∀ d : ℕ, finiteEtaleTateTwist T N A hA d ⟶
      (Sheaf.restrictScalars T.smallEtaleTopology phi).obj
        (finiteEtaleTateTwist T M B hB d)
  | 0 => Functor.LaxMonoidal.ε (Sheaf.restrictScalars T.smallEtaleTopology phi)
  | 1 => (ProEtale.etaleSheafExtendScalarsAdjunction phi T).homEquiv _ _ r.sheafIso.hom
  | d + 2 => (finiteTateEtaleTransition r (d + 1) ⊗ₘ finiteTateEtaleTransition r 1) ≫
      Functor.LaxMonoidal.μ (Sheaf.restrictScalars T.smallEtaleTopology phi)
        (finiteEtaleTateTwist T M B hB (d + 1)) (finiteEtaleTateLine T M B hB)

end AlgebraicGeometry.Scheme.PurityIntegralTower
