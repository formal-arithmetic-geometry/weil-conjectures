/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.FixedFinitePositiveCoefficientTwist
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTensorFamily
import WeilConjectures.SixFunctors.Etale.Derived.LocallyConstantInvertible

/-! # Invertibility of the ordered positive shifted Tate powers

Source: Stacks Tag 03PK, finite Tate line; Tag 0FI5, twisting the projective-bundle basis.
(blueprint: lem-pur-chern-twist-invertible).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v w
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting

private theorem invertible_of_iso {C : Type v} [Category.{w} C] [MonoidalCategory C]
    {X Y : C} (e : X ≅ Y) (h : CategoryTheory.IsInvertible X) :
    CategoryTheory.IsInvertible Y := by
  obtain ⟨Z, ⟨r⟩, ⟨l⟩⟩ := h
  exact ⟨Z, ⟨(e.symm ⊗ᵢ Iso.refl Z) ≪≫ r⟩, ⟨(Iso.refl Z ⊗ᵢ e.symm) ≪≫ l⟩⟩

private theorem invertible_tensor {C : Type v} [Category.{w} C] [MonoidalCategory C]
    {X Y : C} (hX : CategoryTheory.IsInvertible X) (hY : CategoryTheory.IsInvertible Y) :
    CategoryTheory.IsInvertible (X ⊗ Y) := by
  obtain ⟨X', ⟨rX⟩, ⟨lX⟩⟩ := hX
  obtain ⟨Y', ⟨rY⟩, ⟨lY⟩⟩ := hY
  refine ⟨Y' ⊗ X', ⟨?_⟩, ⟨?_⟩⟩
  · exact α_ X Y (Y' ⊗ X') ≪≫
      whiskerLeftIso X (α_ Y Y' X').symm ≪≫
      whiskerLeftIso X (rY ⊗ᵢ Iso.refl X') ≪≫
      whiskerLeftIso X (λ_ X') ≪≫ rX
  · exact α_ Y' X' (X ⊗ Y) ≪≫
      whiskerLeftIso Y' (α_ X' X Y).symm ≪≫
      whiskerLeftIso Y' (lX ⊗ᵢ Iso.refl Y) ≪≫
      whiskerLeftIso Y' (λ_ Y) ≪≫ lY

/-- Every published ordered positive shifted Tate power is tensor-invertible
on a scheme over the fixed field, including the zero power and an empty scheme.
Source: Stacks Tag 03PK, roots-of-unity line, and Tag 0FI5, coefficient twists.
Proof: the finite Tate line has its actual internal dual as a sheaf tensor inverse.
The degree-zero realization of that tensor inverse makes its derived line invertible;
shifting by two preserves invertibility. The zero ordered power is the recorded
coefficient unit, isomorphic to the monoidal unit. Each successor is the previous
ordered power tensored with the shifted line; the inverse is the reversed tensor
of the two inverses, with the associators and unitors displayed in invertible_tensor.
(blueprint: lem-pur-chern-twist-invertible). -/
theorem ordinaryFinitePositiveTwistEtale_isInvertible (P : PurityFiniteSetting.{u})
    {T : Scheme.{u}} (a : T ⟶ Spec (.of P.field.k)) (i : ℕ) :
    CategoryTheory.IsInvertible (P.diagonalTwistEtale T i) := by
  let A := P.Coefficient
  let m := P.diagonalExponent
  let hm := P.diagonalExponent_annihilates
  let t := Scheme.finiteEtaleTateLineInverse T m
    (pow_pos P.coefficients.prime.out.pos P.level) A hm (P.diagonalExponent_isUnit a)
  have hline : CategoryTheory.IsInvertible
      ((Etale.ordinaryFiniteLine A m hm T)⟦(2 : ℤ)⟧) :=
    Etale.DerivedCategory.isInvertible_shift
      (Etale.isInvertible_singleFunctor_obj_of_tensorIso t.rightIso) 2
  induction i with
  | zero =>
    exact invertible_of_iso (Etale.singleFunctorObjUnitIso (ModuleCat.{u + 1} A) T).symm
      isInvertible_unit
  | succ i ih => exact invertible_tensor ih hline

end WeilConjectures.PurityFiniteSetting
