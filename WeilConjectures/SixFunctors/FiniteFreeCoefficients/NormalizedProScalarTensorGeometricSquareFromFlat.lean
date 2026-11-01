/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.FiniteFreeCoefficients.Sites.FiniteFreeCoefficientExtensionData
public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.PreservesTotalTensorKFlatQuasiIsoSupplement
import WeilConjectures.SixFunctors.FiniteFreeCoefficients.NormalizedProScalarTensorGeometricSquareNatTrans
import WeilConjectures.SixFunctors.Supporting.BifunctorKFlatLocalizationExtensionality
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel

/-! # Localization descent for the normalized pro-scalar tensor square -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.MonoidalClosed
open AlgebraicGeometry AlgebraicGeometry.Etale
open scoped CategoryTheory.Functor
namespace WeilConjectures.FiniteFreeCoefficients

/-- Compare the K-flat predicates over an abstract category: checking this unfolding once
generically keeps the kernel from unfolding it at the pro-etale sheaf category. -/
private theorem kFlat_iff_isKFlatForTotalTensor
    {C : Type*} [Category C] [Abelian C] [MonoidalCategory C]
    [MonoidalPreadditive C] [Limits.HasCountableCoproducts C]
    [∀ (U V W Z : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt U V W Z]
    [∀ (U V W : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor U V W]
    [∀ (U V W : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ U V W]
    (P : CochainComplex C ℤ) :
    (HomologicalComplex.quasiIso C (.up ℤ)).kFlat P ↔ P.IsKFlatForTotalTensor :=
  Iff.rfl

set_option linter.unusedVariables false in
/-- Flat representative equalities descend to arbitrary derived inputs.

Source: Stacks Tags 07A4 and 0G7E; the localization part of
`lem-sf-normalized-pro-scalar-tensor-geometric-square`.

Proof: package both displayed routes as natural transformations on the product derived
category. Every complex has a K-flat resolution by the source library's flat-model
resolution theorem. The resolution extensionality lemma chooses complex preimages of
both derived inputs, resolves them, and forms the product of the resulting localization
isomorphisms. Naturality transports the assumed representative equality along this
product isomorphism, and cancellation of its image proves equality at the given pair.
(blueprint: new-sf-normalized-pro-scalar-tensor-geometric-square-from-flat). -/
theorem normalized_pro_scalar_tensor_geometric_square_from_flat
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (X : Scheme.{u}) (μ : Sites.TensorComparison true φ X)
    (hμ : Sites.NormalizedTensor true φ X μ)
    (Y : Scheme.{u}) (e : Y ≅ X) (δ : Sites.TensorComparison true φ Y)
    (hδ : Sites.NormalizedTensor true φ Y δ)
    (hflat : ∀ (P Q : CochainComplex (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)) ℤ),
      CochainComplex.IsKFlatForTotalTensor P → CochainComplex.IsKFlatForTotalTensor Q →
      ((Sites.proScalarPull φ e.hom).hom.app (DerivedCategory.Q.obj P) ⊗ₘ
        (Sites.proScalarPull φ e.hom).hom.app (DerivedCategory.Q.obj Q)) ≫
        δ.inv.app ((Sites.proPull A e.hom).obj (DerivedCategory.Q.obj P),
          (Sites.proPull A e.hom).obj (DerivedCategory.Q.obj Q)) ≫
        (Sites.scalar true φ Y).map
          (ProEtale.leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) e.hom
            (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q)).inv =
      (ProEtale.leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} B) e.hom
        ((Sites.scalar true φ X).obj (DerivedCategory.Q.obj P))
        ((Sites.scalar true φ X).obj (DerivedCategory.Q.obj Q))).inv ≫
        (Sites.proPull B e.hom).map (μ.inv.app
          (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)) ≫
        (Sites.proScalarPull φ e.hom).hom.app
          (DerivedCategory.Q.obj P ⊗ DerivedCategory.Q.obj Q)) :
    ∀ K L : Sites.D true A X,
      ((Sites.proScalarPull φ e.hom).hom.app K ⊗ₘ
        (Sites.proScalarPull φ e.hom).hom.app L) ≫
        δ.inv.app ((Sites.proPull A e.hom).obj K, (Sites.proPull A e.hom).obj L) ≫
        (Sites.scalar true φ Y).map
          (ProEtale.leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) e.hom K L).inv =
      (ProEtale.leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} B) e.hom
        ((Sites.scalar true φ X).obj K) ((Sites.scalar true φ X).obj L)).inv ≫
        (Sites.proPull B e.hom).map (μ.inv.app (K, L)) ≫
        (Sites.proScalarPull φ e.hom).hom.app (K ⊗ L) := by
  intro K L
  obtain ⟨lhs, rhs, hlhs, hrhs⟩ :=
    normalized_pro_scalar_tensor_geometric_square_natTrans φ X μ Y e δ
  have heq : lhs = rhs := by
    apply bifunctor_kflat_localization_extensionality
      (P := CochainComplex.IsKFlatForTotalTensor) ?_ _ _ lhs rhs
    · intro P Q hP hQ
      rw [hlhs, hrhs]
      exact hflat P Q hP hQ
    · intro T
      obtain ⟨P, p, hp, _, hP⟩ := CochainComplex.exists_quasiIso_flat_kFlat T
      exact ⟨P, p, (kFlat_iff_isKFlatForTotalTensor P).mp hP, hp⟩
  calc
    _ = lhs.app (K, L) := (hlhs K L).symm
    _ = rhs.app (K, L) := congrArg (fun z => z.app (K, L)) heq
    _ = _ := hrhs K L

end WeilConjectures.FiniteFreeCoefficients
