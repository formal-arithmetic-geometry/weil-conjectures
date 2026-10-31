/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.FiniteFreeCoefficients.Sites.FiniteFreeCoefficientExtensionData
public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.PreservesTotalTensorKFlatQuasiIsoSupplement

/-! Representative assembly for the normalized pro-scalar tensor square.

Source: Stacks Tags 06YY, 07A4 and 0G7E; the inverse of the monoidal
scalar/pullback tensor law.
Proof: cancel the hom components of the normalized tensor comparison, the
left-derived upper-star tensor isomorphisms, and the scalar/pullback
comparison. The forward square obtained from cochain normalization then
reduces exactly to the displayed inverse-oriented square.
(blueprint: new-sf-normalized-pro-scalar-tensor-geometric-square-on-flat-representative). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.MonoidalClosed
open AlgebraicGeometry AlgebraicGeometry.Etale
open scoped CategoryTheory.Functor
namespace WeilConjectures.FiniteFreeCoefficients

private theorem inverse_square
    {C : Type*} [Category C] {U V W Z S T : C}
    (a : U ⟶ V) (b : V ≅ W) (c : W ≅ Z) (d : U ≅ S) (e : S ≅ T) (t : T ⟶ Z)
    (h : a ≫ b.hom ≫ c.hom = d.hom ≫ e.hom ≫ t) :
    t ≫ c.inv ≫ b.inv = e.inv ≫ d.inv ≫ a := by
  apply (cancel_mono (b.hom ≫ c.hom)).1
  simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id,
    Category.id_comp, Category.comp_id] using
    congrArg (fun z ↦ e.inv ≫ d.inv ≫ z) h.symm

/-- The inverse-oriented square follows from the forward normalized tensor square.
Source: Stacks Tags 06YY, 07A4 and 0G7E.
Proof: postcompose by the geometric and scalar tensorator homs, cancel their
inverses, and use the forward square conjugated by the two other inverse homs.
(blueprint: new-sf-normalized-pro-scalar-tensor-geometric-square-on-flat-representative). -/
theorem normalized_pro_scalar_tensor_geometric_square_representative
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (X : Scheme.{u}) (μ : Sites.TensorComparison true φ X)
    (_hμ : Sites.NormalizedTensor true φ X μ)
    (Y : Scheme.{u}) (e : Y ≅ X) (δ : Sites.TensorComparison true φ Y)
    (_hδ : Sites.NormalizedTensor true φ Y δ)
    (P Q : CochainComplex
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)) ℤ)
    (_hP : CochainComplex.IsKFlatForTotalTensor P)
    (_hQ : CochainComplex.IsKFlatForTotalTensor Q)
    (hcoh :
      (Sites.proScalarPull φ e.hom).hom.app
          (DerivedCategory.Q.obj P ⊗ DerivedCategory.Q.obj Q) ≫
        (Sites.scalar true φ Y).map
          (ProEtale.leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A)
            e.hom (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q)).hom ≫
        δ.hom.app ((Sites.proPull A e.hom).obj (DerivedCategory.Q.obj P),
          (Sites.proPull A e.hom).obj (DerivedCategory.Q.obj Q)) =
      (Sites.proPull B e.hom).map (μ.hom.app
          (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)) ≫
        (ProEtale.leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} B) e.hom
          ((Sites.scalar true φ X).obj (DerivedCategory.Q.obj P))
          ((Sites.scalar true φ X).obj (DerivedCategory.Q.obj Q))).hom ≫
        ((Sites.proScalarPull φ e.hom).hom.app (DerivedCategory.Q.obj P) ⊗ₘ
          (Sites.proScalarPull φ e.hom).hom.app (DerivedCategory.Q.obj Q)))
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
  exact inverse_square
    ((Sites.proScalarPull φ e.hom).hom.app
      (DerivedCategory.Q.obj P ⊗ DerivedCategory.Q.obj Q))
    ((Sites.scalar true φ Y).mapIso
      (ProEtale.leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) e.hom
        (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q)))
    (δ.app ((Sites.proPull A e.hom).obj (DerivedCategory.Q.obj P),
      (Sites.proPull A e.hom).obj (DerivedCategory.Q.obj Q)))
    ((Sites.proPull B e.hom).mapIso (μ.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)))
    (ProEtale.leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} B) e.hom
      ((Sites.scalar true φ X).obj (DerivedCategory.Q.obj P))
      ((Sites.scalar true φ X).obj (DerivedCategory.Q.obj Q)))
    ((Sites.proScalarPull φ e.hom).hom.app (DerivedCategory.Q.obj P) ⊗ₘ
      (Sites.proScalarPull φ e.hom).hom.app (DerivedCategory.Q.obj Q)) hcoh

end WeilConjectures.FiniteFreeCoefficients
