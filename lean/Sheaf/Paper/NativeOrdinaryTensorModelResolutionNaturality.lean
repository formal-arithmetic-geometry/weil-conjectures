/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J6
-/
module

public import Sheaf.Paper.NativeWeilClosedModels
import Sheaf.Paper.NativeOrdinaryTensorModelResolutionData

/-! # Naturality from ordinary tensor resolution transport

Source: Stacks 06YU and 0FPT; blueprint step 1 of
`lem-sf-native-weil-tensor-ringed-derived-square-ordinary-resolution-extension`.
(blueprint: lem-sf-native-weil-tensor-resolution-model-naturality)
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures
namespace AlgebraicGeometry.ProEtaleWeilSheaf

/-- Resolution transport data imply naturality of the extended ordinary model.

Source: Stacks Tags 06YU and 0FPT, the common-roof comparison argument
(blueprint: lem-sf-native-weil-tensor-resolution-model-naturality).

Proof plan: for a map of arbitrary second complexes, choose the K-flat roof
provided by the resolution-lift clause.  Expand both sides with the transport
identity, use the K-flat naturality square for the roof map, and cancel the
localized quasi-isomorphism maps.  Homotopy invariance of `DerivedCategory.Q`
identifies the two composites over the augmentation homotopy. -/
theorem native_ordinary_tensor_model_resolution_naturality
    (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    (H : (DerivedCategory (ProEtale.AdicSheaf l Y))ᵒᵖ ×
      DerivedCategory (ProEtale.AdicSheaf l Y) ⥤
      DerivedCategory (ProEtale.AdicSheaf l Y))
    (R : NativeHomRepresentatives (ordinaryIhomBifunctor l Y) H)
    (S : CoefficientClosedStructure H)
    (model : ∀ (P Q : CochainComplex (ProEtale.AdicSheaf l Y) ℤ)
      (_ : NativeOrdinaryKFlat l Y P),
      S.tensor.obj (DerivedCategory.Q.obj Q, DerivedCategory.Q.obj P) ≅
        DerivedCategory.Q.obj (ordinaryTensorTotal l Y P Q))
    (extendedModel : ∀ (P Q : CochainComplex (ProEtale.AdicSheaf l Y) ℤ)
      (_ : NativeOrdinaryKFlat l Y P),
      S.tensor.obj (DerivedCategory.Q.obj Q, DerivedCategory.Q.obj P) ≅
        DerivedCategory.Q.obj (ordinaryTensorTotal l Y P Q))
    (htransport : ∀ (P Q K : CochainComplex (ProEtale.AdicSheaf l Y) ℤ)
      (hP : NativeOrdinaryKFlat l Y P)
      (hK : NativeOrdinaryKFlat l Y K)
      (q : K ⟶ Q) (hq : QuasiIso q),
      S.tensor.map
          (X := (DerivedCategory.Q.obj K, DerivedCategory.Q.obj P))
          (Y := (DerivedCategory.Q.obj Q, DerivedCategory.Q.obj P))
          (Prod.mkHom (DerivedCategory.Q.map q) (𝟙 _)) ≫
          (extendedModel P Q hP).hom =
        (model P K hP).hom ≫ DerivedCategory.Q.map
          (HomologicalComplex.mapBifunctorMap (𝟙 P) q
            (ordinaryTensorBifunctor l Y) (.up ℤ)))
    (hresolution : ∀ (Q Q' : CochainComplex (ProEtale.AdicSheaf l Y) ℤ)
      (g : Q ⟶ Q'),
      ∃ (K K' : CochainComplex (ProEtale.AdicSheaf l Y) ℤ)
        (hK : NativeOrdinaryKFlat l Y K)
        (hK' : NativeOrdinaryKFlat l Y K')
        (q : K ⟶ Q) (q' : K' ⟶ Q') (u : K ⟶ K'),
        QuasiIso q ∧ QuasiIso q' ∧ Nonempty (Homotopy (u ≫ q') (q ≫ g)))
    (hkflat : ∀ (P Q P' Q' : CochainComplex (ProEtale.AdicSheaf l Y) ℤ)
      (hP : NativeOrdinaryKFlat l Y P)
      (hP' : NativeOrdinaryKFlat l Y P')
      (hQ : NativeOrdinaryKFlat l Y Q)
      (hQ' : NativeOrdinaryKFlat l Y Q')
      (f : P ⟶ P') (g : Q ⟶ Q'),
      S.tensor.map
          (X := (DerivedCategory.Q.obj Q, DerivedCategory.Q.obj P))
          (Y := (DerivedCategory.Q.obj Q', DerivedCategory.Q.obj P'))
          (Prod.mkHom (DerivedCategory.Q.map g) (DerivedCategory.Q.map f)) ≫
          (model P' Q' hP').hom =
        (model P Q hP).hom ≫ DerivedCategory.Q.map
          (HomologicalComplex.mapBifunctorMap f g
            (ordinaryTensorBifunctor l Y) (.up ℤ))) :
    ∀ (P Q P' Q' : CochainComplex (ProEtale.AdicSheaf l Y) ℤ)
      (hP : NativeOrdinaryKFlat l Y P)
      (hP' : NativeOrdinaryKFlat l Y P')
      (f : P ⟶ P') (g : Q ⟶ Q'),
      S.tensor.map
          (X := (DerivedCategory.Q.obj Q, DerivedCategory.Q.obj P))
          (Y := (DerivedCategory.Q.obj Q', DerivedCategory.Q.obj P'))
          (Prod.mkHom (DerivedCategory.Q.map g) (DerivedCategory.Q.map f)) ≫
          (extendedModel P' Q' hP').hom =
        (extendedModel P Q hP).hom ≫ DerivedCategory.Q.map
          (HomologicalComplex.mapBifunctorMap f g
            (ordinaryTensorBifunctor l Y) (.up ℤ)) := by
  sorry

end AlgebraicGeometry.ProEtaleWeilSheaf
