/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.Abelian.Projective.Resolution
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Sheaf.Algebra.Homology.KFlat
public import Sheaf.Paper.DerivedHomMayerVietoris
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.Algebra.Homology.HomotopyCategory.SingleFunctors

/-! # Naturality of affine ordinary tensor homology coordinates

Source: Stacks Project, Tags 08DX(2), 08DV, 06YT and 01I9.
(blueprint: new-j1-qcoh-ordinary-tensor-resolution-coordinates-naturality).

The missing argument is the joint naturality of the common K-flat tensor-resolution
zigzag.  The statement is separated from the construction of the chart coordinates.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
open scoped TensorProduct
namespace AlgebraicGeometry

/-- Independence of a supplied affine tensor comparison.

Source: Stacks Project, Tags 06YT and 01I9.
Proof: compare the restricted K-flat tensor-resolution zigzags through a common K-flat
refinement.  Tensor functoriality and the supplied augmentation, coefficient, and pure-
tensor equations commute the squares.  Taking homology and cancelling the invertible
comparison legs transfers the restriction equation from one augmented comparison to every
supplied comparison.  The section formulas for sM and sN are retained throughout.
(blueprint: new-j1-qcoh-ordinary-tensor-resolution-comparison-independence).
-/
theorem qcoh_ordinary_tensor_resolution_comparison_independence
    (Y : Scheme.{u}) (M N : SheafOfModules.{u} (moduleRings Y.toRingedSpace))
    [M.IsQuasicoherent] [N.IsQuasicoherent]
    (MA NA : ∀ U : Y.affineOpens, ModuleCat.{u} (Γ(Y, U.1) : Type u))
    (sM : ∀ U : Y.affineOpens, MA U ≃ₗ[Γ(Y, U.1)] M.val.obj (op U.1))
    (sN : ∀ U : Y.affineOpens, NA U ≃ₗ[Γ(Y, U.1)] N.val.obj (op U.1))
    (P : ∀ U : Y.affineOpens, ProjectiveResolution (MA U))
    (K : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
    (q : K ⟶ (CochainComplex.singleFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj M)
    (hK : CochainComplex.IsKFlat (R := Y.sheaf) K) (hq : QuasiIso q) (n : ℕ) :
    letI := SheafOfModules.monoidalCategory Y.sheaf
    let S := CochainComplex.singleFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0
    let Q := (CochainComplex.mapBifunctor K (S.obj N)
      (curriedTensor (SheafOfModules.{u} (moduleRings Y.toRingedSpace)))).homology
        (-(n : ℤ))
    ∀ c : ∀ U : Y.affineOpens,
        ((((tensorRight (NA U)).mapHomologicalComplex (.down ℕ)).obj
          (P U).complex).homology n) ≃ₗ[Γ(Y, U.1)] Q.val.obj (op U.1),
      (∀ (V U : Y.affineOpens) (h : V.1 ≤ U.1)
        (_hbasic : ∃ f : Γ(Y, U.1), Y.basicOpen f = V.1),
        let φ := (Y.presheaf.map (homOfLE h).op).hom
        let TA := (tensorRight (NA U)).mapHomologicalComplex (.down ℕ)
        let TC := (tensorRight (NA V)).mapHomologicalComplex (.down ℕ)
        ∃ (b : NA U →ₛₗ[φ] NA V)
          (a : (P U).complex ⟶ ((ModuleCat.restrictScalars φ).mapHomologicalComplex
            (.down ℕ)).obj (P V).complex)
          (k : TA.obj (P U).complex ⟶
            ((ModuleCat.restrictScalars φ).mapHomologicalComplex (.down ℕ)).obj
              (TC.obj (P V).complex)),
          (∀ x : (P U).complex.X 0,
            sM V ((P V).π.f 0 (a.f 0 x)) =
              M.val.map (homOfLE h).op (sM U ((P U).π.f 0 x))) ∧
          (∀ y : NA U, sN V (b y) = N.val.map (homOfLE h).op (sN U y)) ∧
          (∀ (j : ℕ) (x : (P U).complex.X j) (y : NA U),
            k.f j (x ⊗ₜ[Γ(Y, U.1)] y) =
              (show (P V).complex.X j from a.f j x) ⊗ₜ[Γ(Y, V.1)] (b y)) ∧
          let e := ((TC.obj (P V).complex).sc n).mapHomologyIso
            (ModuleCat.restrictScalars φ)
          ∀ x, Q.val.map (homOfLE h).op (c U x) =
            c V (e.hom (HomologicalComplex.homologyMap k n x))) →
      ∀ (V U : Y.affineOpens) (h : V.1 ≤ U.1)
        (_hbasic : ∃ f : Γ(Y, U.1), Y.basicOpen f = V.1),
        let φ := (Y.presheaf.map (homOfLE h).op).hom
        let TA := (tensorRight (NA U)).mapHomologicalComplex (.down ℕ)
        let TC := (tensorRight (NA V)).mapHomologicalComplex (.down ℕ)
        ∀ (b : NA U →ₛₗ[φ] NA V)
          (a : (P U).complex ⟶ ((ModuleCat.restrictScalars φ).mapHomologicalComplex
            (.down ℕ)).obj (P V).complex)
          (k : TA.obj (P U).complex ⟶
            ((ModuleCat.restrictScalars φ).mapHomologicalComplex (.down ℕ)).obj
              (TC.obj (P V).complex)),
          (∀ x : (P U).complex.X 0,
            sM V ((P V).π.f 0 (a.f 0 x)) =
              M.val.map (homOfLE h).op (sM U ((P U).π.f 0 x))) →
          (∀ y : NA U, sN V (b y) = N.val.map (homOfLE h).op (sN U y)) →
          (∀ (j : ℕ) (x : (P U).complex.X j) (y : NA U),
            k.f j (x ⊗ₜ[Γ(Y, U.1)] y) =
              (show (P V).complex.X j from a.f j x) ⊗ₜ[Γ(Y, V.1)] (b y)) →
          let e := ((TC.obj (P V).complex).sc n).mapHomologyIso
            (ModuleCat.restrictScalars φ)
          ∀ x, Q.val.map (homOfLE h).op (c U x) =
            c V (e.hom (HomologicalComplex.homologyMap k n x)) := by
  sorry

end AlgebraicGeometry
