/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.Native.Weil.NativeWeilClosedModels
import WeilConjectures.WeilSheaf.Native.Ordinary.NativeOrdinaryTensorModelResolutionTransport
import WeilConjectures.WeilSheaf.Native.Ordinary.NativeOrdinaryTensorModelResolutionRoof

/-! # Resolution transport data for ordinary tensor models

## Implementation details

The resolved model is obtained from the degreewise-epimorphic K-flat resolution supplied by
`CochainComplex.exists_isKFlatResolutionIndependentCoefficients`: tensoring its augmentation
with a K-flat first input is a quasi-isomorphism, and the supplied K-flat model is composed
with the inverse of its localization. Independence of two resolutions gives the restriction
equation, and the same construction on a common K-flat roof supplies the lift property used
by the naturality theorem.

## References

* Stacks Project, Tags 06YS, 06YU and 0FPT
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures
namespace AlgebraicGeometry.ProEtaleWeilSheaf

/-- The model and its comparison equations obtained by resolving the second input. -/
theorem native_ordinary_tensor_model_resolution_data
    (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    (H : (DerivedCategory (ProEtale.AdicSheaf l Y))ᵒᵖ ×
      DerivedCategory (ProEtale.AdicSheaf l Y) ⥤
      DerivedCategory (ProEtale.AdicSheaf l Y))
    (_R : NativeHomRepresentatives (ordinaryIhomBifunctor l Y) H)
    (S : CoefficientClosedStructure H)
    (model : ∀ (P Q : CochainComplex (ProEtale.AdicSheaf l Y) ℤ)
      (_ : NativeOrdinaryKFlat l Y P),
      S.tensor.obj (DerivedCategory.Q.obj Q, DerivedCategory.Q.obj P) ≅
        DerivedCategory.Q.obj (ordinaryTensorTotal l Y P Q))
    (hkflat : ∀ (P Q P' Q' : CochainComplex (ProEtale.AdicSheaf l Y) ℤ)
      (hP : NativeOrdinaryKFlat l Y P)
      (hP' : NativeOrdinaryKFlat l Y P')
      (_hQ : NativeOrdinaryKFlat l Y Q)
      (_hQ' : NativeOrdinaryKFlat l Y Q')
      (f : P ⟶ P') (g : Q ⟶ Q'),
      S.tensor.map
          (X := (DerivedCategory.Q.obj Q, DerivedCategory.Q.obj P))
          (Y := (DerivedCategory.Q.obj Q', DerivedCategory.Q.obj P'))
          (Prod.mkHom (DerivedCategory.Q.map g) (DerivedCategory.Q.map f)) ≫
          (model P' Q' hP').hom =
        (model P Q hP).hom ≫ DerivedCategory.Q.map
          (HomologicalComplex.mapBifunctorMap f g
            (ordinaryTensorBifunctor l Y) (.up ℤ))) :
    ∃ extendedModel : ∀ (P Q : CochainComplex (ProEtale.AdicSheaf l Y) ℤ)
      (_ : NativeOrdinaryKFlat l Y P),
      S.tensor.obj (DerivedCategory.Q.obj Q, DerivedCategory.Q.obj P) ≅
        DerivedCategory.Q.obj (ordinaryTensorTotal l Y P Q),
      (∀ (P Q : CochainComplex (ProEtale.AdicSheaf l Y) ℤ)
        (hP : NativeOrdinaryKFlat l Y P)
        (_hQ : NativeOrdinaryKFlat l Y Q),
        extendedModel P Q hP = model P Q hP) ∧
      (∀ (P Q K : CochainComplex (ProEtale.AdicSheaf l Y) ℤ)
        (hP : NativeOrdinaryKFlat l Y P)
        (_hK : NativeOrdinaryKFlat l Y K)
        (q : K ⟶ Q) (_hq : QuasiIso q),
        S.tensor.map
            (X := (DerivedCategory.Q.obj K, DerivedCategory.Q.obj P))
            (Y := (DerivedCategory.Q.obj Q, DerivedCategory.Q.obj P))
            (Prod.mkHom (DerivedCategory.Q.map q) (𝟙 _)) ≫
            (extendedModel P Q hP).hom =
          (model P K hP).hom ≫ DerivedCategory.Q.map
            (HomologicalComplex.mapBifunctorMap (𝟙 P) q
              (ordinaryTensorBifunctor l Y) (.up ℤ))) ∧
      (∀ (Q Q' : CochainComplex (ProEtale.AdicSheaf l Y) ℤ) (g : Q ⟶ Q'),
        ∃ (K K' : CochainComplex (ProEtale.AdicSheaf l Y) ℤ)
          (_hK : NativeOrdinaryKFlat l Y K)
          (_hK' : NativeOrdinaryKFlat l Y K')
          (q : K ⟶ Q) (q' : K' ⟶ Q') (u : K ⟶ K'),
          QuasiIso q ∧ QuasiIso q' ∧ Nonempty (Homotopy (u ≫ q') (q ≫ g))) := by
  classical
  obtain ⟨extendedModel, hrestrict, htransport⟩ :=
    native_ordinary_tensor_model_resolution_transport l Y H S model hkflat
  obtain hresolution := native_ordinary_tensor_model_resolution_roof l Y
  exact ⟨extendedModel, hrestrict, htransport, hresolution⟩

end AlgebraicGeometry.ProEtaleWeilSheaf
