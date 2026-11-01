/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.FiniteFreeCoefficients.Sites.FiniteFreeCoefficientExtensionData
public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.PreservesTotalTensorKFlatQuasiIsoSupplement
public import WeilConjectures.SixFunctors.FiniteFreeCoefficients.NormalizedProScalarTensorGeometricSquareOnFlatRepresentative
public import WeilConjectures.SixFunctors.FiniteFreeCoefficients.NormalizedProScalarTensorGeometricSquareOnFlatTensorCoherence

/-! # Flat representative form of the normalized pro-scalar tensor square -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.MonoidalClosed
open AlgebraicGeometry AlgebraicGeometry.Etale
open scoped CategoryTheory.Functor
namespace WeilConjectures.FiniteFreeCoefficients

/-- The scalar/tensor geometric square on flat K-flat representatives.

Source: Stacks Tags 06YY, 07A4 and 0G7E; the flat representative part of
`lem-sf-normalized-pro-scalar-tensor-geometric-square`.

Proof: for K-flat representatives P and Q, expand the
normalized pro-etale scalar/tensor comparisons through their ordinary balancing
maps. Exact inverse image along a scheme isomorphism preserves the representatives,
and the two balancing composites agree on pure tensors. The Koszul total differential
has the same signed Leibniz rule on both routes, so the equality descends through the
localization tensor counits. The remaining identification is the mate equation for
the canonical scalar/pullback comparison.
(blueprint: new-sf-normalized-pro-scalar-tensor-geometric-square-on-flat). -/
theorem normalized_pro_scalar_tensor_geometric_square_on_flat
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (X : Scheme.{u}) (μ : Sites.TensorComparison true φ X)
    (hμ : Sites.NormalizedTensor true φ X μ)
    (Y : Scheme.{u}) (e : Y ≅ X) (δ : Sites.TensorComparison true φ Y)
    (hδ : Sites.NormalizedTensor true φ Y δ)
    (P Q : CochainComplex (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)) ℤ)
    (hP : CochainComplex.IsKFlatForTotalTensor P) (hQ : CochainComplex.IsKFlatForTotalTensor Q)
    :
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
          (DerivedCategory.Q.obj P ⊗ DerivedCategory.Q.obj Q) := by
  have hcoh := pro_scalar_pullback_tensor_cochain_square
    φ X μ hμ Y e δ hδ P Q hP hQ
  exact normalized_pro_scalar_tensor_geometric_square_representative
    φ X μ hμ Y e δ hδ P Q hP hQ hcoh

end WeilConjectures.FiniteFreeCoefficients
