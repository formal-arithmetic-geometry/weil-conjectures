/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedProjectiveLineConstantDecomposition
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.CategoryTheory.SixFunctors.LocalizingClosure
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Rational.RationalLocalizingProjectionFormula
import WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientDescentTwoColimit
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleTensorObj
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory
import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory

/-! # Tensoring the condensed projective-line decomposition -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj
attribute [local instance] preservesBinaryBiproducts_of_preservesBiproducts
namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The constant projective-line decomposition extends to a coefficient object in the
localizing constructible category by the proper projection formula.
Source: current blueprint, `thm-amb-p1-decomposition.proof.md`, projection-formula paragraph.
(blueprint: lem-pur-condensed-p1-tensor-decomposition).

Proof: apply the proper projection formula with its first argument the coefficient unit.
Tensor the constant decomposition with B, distribute over the finite biproduct, cancel
the left unit and commute tensor with the shift. No choice of a cohomology-class lift
or Frobenius-equivariant derived arrow is involved.
-/
theorem exists_projectiveLine_tensor_decomposition
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (S : Scheme.{u}) [S.Over (Spec (.of k))]
    [IsSeparated (S ↘ Spec (.of k))]
    [LocallyOfFiniteType (S ↘ Spec (.of k))] [QuasiCompact (S ↘ Spec (.of k))]
    (B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) S)))
    (hB : localizingClosure
      (constantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ) S) B) :
    Nonempty ((moduleObjectDerivedPushforward (Profinite.padicAlgClRingObj ℓ)
        (ProjectiveLine S ↘ S)).obj
        ((moduleObjectDerivedPullback (Profinite.padicAlgClRingObj ℓ)
          (ProjectiveLine S ↘ S)).obj B) ≅
      B ⊞ ((shiftFunctor _ (-2 : ℤ)).obj (tateTwistDerived S ℓ (-1) ⊗ B))) := by
  have : LocallyOfFiniteType (ProjectiveLine S ↘ Spec (.of k)) := by
    rw [← comp_over (ProjectiveLine S ↘ S) (Spec (.of k))]
    infer_instance
  have : QuasiCompact (ProjectiveLine S ↘ Spec (.of k)) := by
    rw [← comp_over (ProjectiveLine S ↘ S) (Spec (.of k))]
    infer_instance
  have : IsSeparated (ProjectiveLine S ↘ Spec (.of k)) := by
    rw [← comp_over (ProjectiveLine S ↘ S) (Spec (.of k))]
    infer_instance
  let Λ := Profinite.padicAlgClRingObj ℓ
  let q := ProjectiveLine S ↘ S
  let R := moduleObjectDerivedPushforward Λ q
  let L := moduleObjectDerivedPullback Λ q
  obtain ⟨d, _⟩ := exists_condensed_projectiveLine_constant_decomposition
    (ringChar k) ℓ (Ne.symm (Fact.out : ringChar k ≠ ℓ)) k S (S ↘ Spec (.of k))
  have hbc := (finiteCoefficientDescentTwoColimit k (ringChar k) ℓ
    (Fact.out : (ringChar k).Prime).pos Fact.out (ProjectiveLine S)).2.2.2.2.1.1
  have hA : localizingClosure (constantModelBoundedConstructible Λ (ProjectiveLine S))
      (𝟙_ _) := by
    intro P hP h
    apply h
    rw [hbc]
    exact boundedConstructible_tensorUnit Λ (ProjectiveLine S)
  have := (isIso_projectionMate_localizing_padicAlgCl ℓ k q (𝟙_ _) B hA hB).2.2
  let e : R.obj (𝟙_ _) ⊗ B ≅ R.obj ((𝟙_ _) ⊗ L.obj B) :=
    asIso (moduleObjectProjectionMate Λ q (𝟙_ _) B)
  exact ⟨(R.mapIso (λ_ (L.obj B))).symm ≪≫ e.symm ≪≫
    tensorIso d.symm (Iso.refl B) ≪≫
    (tensorRight B).mapBiprod _ _ ≪≫
    biprod.mapIso (λ_ B) (((tensorRight B).commShiftIso (-2 : ℤ)).app
      (tateTwistDerived S ℓ (-1)))⟩

end AlgebraicGeometry.ProEtale.CondensedRing
