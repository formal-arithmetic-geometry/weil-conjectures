/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.DerivedWeilTensorOperations
import all Sheaf.Paper.NativeTensorAcyclicTestComparison
import Sheaf.Paper.NativeWeilTensorRingedKFlatLocalization

/-! # Natural native tensor model comparisons -/

@[expose] public noncomputable section
set_option autoImplicit false

attribute [local irreducible]
  AlgebraicGeometry.ProEtaleWeilSheaf.nativeDerivedClosedComparison
  AlgebraicGeometry.ProEtaleWeilSheaf.nativeDerivedTensor
  AlgebraicGeometry.ProEtaleWeilSheaf.nativeTensorTotal
  AlgebraicGeometry.ProEtaleWeilSheaf.NativeIsKFlat

universe u v₁ v₂ w₁ w₂
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtaleWeilSheaf

private theorem native_flat_family (k₀ : Type u) [Field k₀] [Finite k₀]
    (l : ℕ) [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
    (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
    (P : ObjectProperty.FullSubcategory
      (NativeTensorKFlat k₀ l X (nativeTensorBifunctor k₀ l X))) :
    FlatTest k₀ l X P.obj :=
  ⟨native_tensor_acyclic_test_kflat k₀ l X P.obj P.property⟩

private theorem native_flat_localization (k₀ : Type u) [Field k₀] [Finite k₀]
    (l : ℕ) [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
    (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    [IsSeparated (X ↘ Spec (CommRingCat.of k₀))] :
    ((ObjectProperty.ι (NativeTensorKFlat k₀ l X (nativeTensorBifunctor k₀ l X))) ⋙
      DerivedCategory.Q).IsLocalization
        ((HomologicalComplex.quasiIso (ProEtaleWeilSheaf k₀ l X) (.up ℤ)).inverseImage
          (ObjectProperty.ι (NativeTensorKFlat k₀ l X (nativeTensorBifunctor k₀ l X)))) :=
  native_weil_tensor_ringed_kflat_localization _

/-- Natural tensor model comparisons along any two families of K-flat complexes.

Source: Stacks 06YN and the native derived tensor model theorem.
(blueprint: new-sf-native-tensor-model-comparison).

Proof: choose the natural model isomorphisms supplied by nativeDerivedTensor_models.
Evaluate them on the two given families. Their simultaneous naturality is exactly
the naturality condition for the uncurry of the total tensor bifunctor. Thus
NatIso.ofComponents assembles the required natural isomorphism. -/
theorem native_tensor_model_comparison (k₀ : Type u) [Field k₀] [Finite k₀]
    (l : ℕ) [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
    (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
    {A : Type v₁} {B : Type v₂} [Category.{w₁} A] [Category.{w₂} B]
    (F : A ⥤ CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ)
    (G : B ⥤ CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ)
    (hF : ∀ P, NativeIsKFlat k₀ l X (F.obj P))
    (hG : ∀ T, NativeIsKFlat k₀ l X (G.obj T)) :
    Nonempty ((F ⋙ DerivedCategory.Q).prod (G ⋙ DerivedCategory.Q) ⋙
        nativeDerivedTensor k₀ l X ≅
      F.prod G ⋙ Functor.uncurry.obj (nativeTensorTotal k₀ l X) ⋙ DerivedCategory.Q) := by
  obtain ⟨e, hn⟩ := nativeDerivedTensor_models k₀ l X
  exact NativeOpenComparisonProof.models DerivedCategory.Q (nativeTensorTotal k₀ l X)
    (nativeDerivedTensor k₀ l X) (NativeIsKFlat k₀ l X) (NativeIsKFlat k₀ l X)
    (fun _ h ↦ h) e hn F G hF hG

end AlgebraicGeometry.ProEtaleWeilSheaf
