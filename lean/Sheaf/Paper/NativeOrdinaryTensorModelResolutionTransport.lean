/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J2
-/
module

public import Sheaf.Paper.NativeWeilClosedModels

/-! # Transport part of ordinary tensor resolution data

Source: Stacks 06YS, 06YU; blueprint step 1 of
`lem-sf-native-weil-tensor-ringed-derived-square-ordinary-resolution-extension`.
(blueprint: lem-sf-native-weil-tensor-resolution-model-transport)
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedVariables false
universe u
open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures
namespace AlgebraicGeometry.ProEtaleWeilSheaf

/--
The K-flat resolution construction supplies an ordinary tensor model on every
second complex, together with its restriction to K-flat inputs and its
augmentation transport identity.  The common-roof assertion is separated into
`native_ordinary_tensor_model_resolution_roof`.

Source: Stacks Tags 06YS and 06YU, K-flat replacement and resolution-comparison
paragraph in the ordinary tensor construction.  Choose a degreewise-epimorphic
K-flat resolution of the second input, tensor its augmentation with the K-flat
first input, and invert the resulting localized quasi-isomorphism.  Independence
of two such resolutions gives the restriction equation.  The localization
square gives the transport equation.
(blueprint: lem-sf-native-weil-tensor-resolution-model-transport)
-/
theorem native_ordinary_tensor_model_resolution_transport
    (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    (H : (DerivedCategory (ProEtale.AdicSheaf l Y))ᵒᵖ ×
      DerivedCategory (ProEtale.AdicSheaf l Y) ⥤
      DerivedCategory (ProEtale.AdicSheaf l Y))
    (S : CoefficientClosedStructure H)
    (model : ∀ (P Q : CochainComplex (ProEtale.AdicSheaf l Y) ℤ)
      (_ : NativeOrdinaryKFlat l Y P),
      S.tensor.obj (DerivedCategory.Q.obj Q, DerivedCategory.Q.obj P) ≅
        DerivedCategory.Q.obj (ordinaryTensorTotal l Y P Q))
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
    ∃ extendedModel : ∀ (P Q : CochainComplex (ProEtale.AdicSheaf l Y) ℤ)
      (_ : NativeOrdinaryKFlat l Y P),
      S.tensor.obj (DerivedCategory.Q.obj Q, DerivedCategory.Q.obj P) ≅
        DerivedCategory.Q.obj (ordinaryTensorTotal l Y P Q),
      (∀ (P Q : CochainComplex (ProEtale.AdicSheaf l Y) ℤ)
        (hP : NativeOrdinaryKFlat l Y P)
        (hQ : NativeOrdinaryKFlat l Y Q),
        extendedModel P Q hP = model P Q hP) ∧
      (∀ (P Q K : CochainComplex (ProEtale.AdicSheaf l Y) ℤ)
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
              (ordinaryTensorBifunctor l Y) (.up ℤ))) := by
  sorry

end AlgebraicGeometry.ProEtaleWeilSheaf
