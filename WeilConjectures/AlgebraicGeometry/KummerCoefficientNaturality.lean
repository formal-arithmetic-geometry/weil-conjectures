/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Kummer.KummerModuleCoefficients

/-! # Kummer coefficient insertion commutes with coefficient maps
Source: det-prop-a1-kummer.proof.md, Coefficients and Degrees 0 and 1.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
namespace AlgebraicGeometry.Scheme

private theorem coefficient_insertion_map (X : Scheme.{u}) (m : ℕ)
    {A B : ModuleCat.{u + 1} (ULift.{u + 1} (ZMod m))} (f : A ⟶ B) (a : A) :
    kummerCoefficientInsertion X m A a ≫ (kummerAbelianTwist X m).map f =
      kummerCoefficientInsertion X m B (f a) := by
  apply Sheaf.hom_ext
  ext U x
  let R := kummerRootModulePresheaf X m
  let P := R ⊗ (Functor.const X.Etaleᵒᵖ).obj A
  let Q := R ⊗ (Functor.const X.Etaleᵒᵖ).obj B
  let φ : P ⟶ Q := (tensorLeft R).map ((Functor.const X.Etaleᵒᵖ).map f)
  have h := congrArg (fun k ↦ k.hom (TensorProduct.tmul _ x a))
    (congr_app (toSheafify_naturality X.smallEtaleTopology φ) U)
  change ((toSheafify X.smallEtaleTopology Q).app U).hom
      ((φ.app U).hom (TensorProduct.tmul _ x a)) =
    ((sheafifyMap X.smallEtaleTopology φ).app U).hom
      (((toSheafify X.smallEtaleTopology P).app U).hom (TensorProduct.tmul _ x a)) at h
  have hφ : (φ.app U).hom (TensorProduct.tmul _ (x : R.obj U) a) =
      TensorProduct.tmul (ULift.{u + 1} (ZMod m)) (M := R.obj U) (N := B) x (f a) := by rfl
  rw [hφ] at h
  exact h.symm

/-- The actual insertion maps commute with every coefficient-linear map in all degrees.
Source: det-prop-a1-kummer.proof.md, uniformizer coefficient induction
(blueprint: new-pur-kummer-coefficient-insertion-naturality).

Proof: before sheafification the coefficient map sends x tensor a to x tensor f(a).
Naturality of the sheafification unit gives equality of the two sheaf morphisms.
Apply the functorial composition identity for ordinary sheaf cohomology. This applies
to arbitrary modules and every q, including the zero module and q=0; no flatness is used. -/
theorem kummerCoefficientInsertion_cohomology_map (X : Scheme.{u}) (m : ℕ)
    {A B : ModuleCat.{u + 1} (ULift.{u + 1} (ZMod m))} (f : A ⟶ B) (a : A)
    (q : ℕ) (x : Sheaf.H (X.rootsOfUnitySheaf m) q) :
    Sheaf.H.map ((kummerAbelianTwist X m).map f) q
        (Sheaf.H.map (kummerCoefficientInsertion X m A a) q x) =
      Sheaf.H.map (kummerCoefficientInsertion X m B (f a)) q x := by
  rw [← Sheaf.H.map_comp_apply, coefficient_insertion_map]

end AlgebraicGeometry.Scheme
