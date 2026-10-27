/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E7
-/
module

public import Sheaf.Paper.NativeWeilClosedModels

/-! # Naturality on K-flat ordinary tensor representatives

The normalization condition determines the representative comparison by its
tensor--Hom transpose when both representative inputs are K-flat.  This is the
K-flat part of the ordinary naturality argument.

Source: Stacks 06YU, 0FPT; blueprint step 1 of
`lem-sf-native-weil-tensor-ringed-derived-square-ordinary-data`.
(blueprint: lem-sf-native-weil-tensor-ringed-derived-square-ordinary-naturality)
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures
namespace AlgebraicGeometry.ProEtaleWeilSheaf

/-- A normalized one-K-flat ordinary tensor model is natural on K-flat inputs.

The proof compares both sides after applying the specified product-total Hom
representatives.  The componentwise uncurrying equation in
`NativeAdjunctionNormalization` identifies their transposes, and the
tensor--Hom adjunction then cancels the common transpose.  Both Q and Q' are
assumed K-flat here; the extension to arbitrary second inputs is a separate
resolution argument. -/
theorem native_ordinary_tensor_model_naturality_kflat
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
    (_hnormalization : NativeAdjunctionNormalization
      (ordinaryIhomBifunctor l Y) (ordinaryTensorBifunctor l Y)
      (fun P ↦ Mod.ihomAdjunction P) H R S
      (NativeOrdinaryKFlat l Y) model) :
    ∀ (P Q P' Q' : CochainComplex (ProEtale.AdicSheaf l Y) ℤ)
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
            (ordinaryTensorBifunctor l Y) (.up ℤ)) := by
  sorry

end AlgebraicGeometry.ProEtaleWeilSheaf
