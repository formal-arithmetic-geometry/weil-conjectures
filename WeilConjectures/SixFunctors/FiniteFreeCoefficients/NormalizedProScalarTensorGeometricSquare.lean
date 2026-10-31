/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.FiniteFreeCoefficients.Sites.FiniteFreeCoefficientExtensionData
import WeilConjectures.SixFunctors.FiniteFreeCoefficients.NormalizedProScalarTensorGeometricSquareFromFlat
import WeilConjectures.SixFunctors.FiniteFreeCoefficients.NormalizedProScalarTensorGeometricSquareOnFlat

/-! # The normalized pro-etale scalar and geometric tensor square -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local irreducible] CategoryTheory.Functor.leftDerivedFunctor
  CategoryTheory.Functor.rightDerivedFunctor CategoryTheory.Functor.mapDerivedCategory
  DerivedCategory.monoidalClosed
  DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory
universe u
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.MonoidalClosed
open AlgebraicGeometry AlgebraicGeometry.Etale
open scoped CategoryTheory.Functor
namespace WeilConjectures.FiniteFreeCoefficients

/-- Representative-normalized pro-etale tensorators respect geometric reindexing.
Source: blueprint latest, lem-coef-finite-free-extension.proof.md, final paragraph.
(blueprint: lem-sf-normalized-pro-scalar-tensor-geometric-square).
Proof: use flat K-flat cochain representatives in both tensor variables. The
normalization equations for mu and delta identify their comparison with the
ordinary sheafified balancing map. Pullback along the scheme isomorphism is exact
reindexing and preserves flat objects and these representatives. Its tensor
comparison is normalized by the cochain tensor counit. The canonical proScalarPull
is the mate of restriction/pullback balancing; transpose its representative square
under scalar extension/restriction to identify it with the same degreewise
balancing map. On a pure tensor, both routes are b tensor (k tensor l) sent to
(b tensor k) tensor (1 tensor l), with reindexing unchanged. Balancing proves
this equality on sheaves, and the Koszul total tensor differential preserves it
on cochains. Apply the localization counits and cancel their K-flat
isomorphisms. Naturality and K-flat resolutions in both variables extend the
square to all derived objects. Invert the two tensor isomorphisms to obtain the
displayed orientation. Neither coefficient flatness nor constructibility is used. -/
theorem normalized_pro_scalar_tensor_geometric_square
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (X : Scheme.{u}) (μ : Sites.TensorComparison true φ X)
    (hμ : Sites.NormalizedTensor true φ X μ)
    (Y : Scheme.{u}) (e : Y ≅ X) (δ : Sites.TensorComparison true φ Y)
    (hδ : Sites.NormalizedTensor true φ Y δ) (K L : Sites.D true A X) :
      ((Sites.proScalarPull φ e.hom).hom.app K ⊗ₘ
        (Sites.proScalarPull φ e.hom).hom.app L) ≫
        δ.inv.app ((Sites.proPull A e.hom).obj K, (Sites.proPull A e.hom).obj L) ≫
        (Sites.scalar true φ Y).map
          (ProEtale.leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) e.hom K L).inv =
      (ProEtale.leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} B) e.hom
        ((Sites.scalar true φ X).obj K) ((Sites.scalar true φ X).obj L)).inv ≫
        (Sites.proPull B e.hom).map (μ.inv.app (K, L)) ≫
        (Sites.proScalarPull φ e.hom).hom.app (K ⊗ L) := by
  apply normalized_pro_scalar_tensor_geometric_square_from_flat φ X μ hμ Y e δ hδ
  intro P Q hP hQ
  exact normalized_pro_scalar_tensor_geometric_square_on_flat φ X μ hμ Y e δ hδ P Q hP hQ

end WeilConjectures.FiniteFreeCoefficients
