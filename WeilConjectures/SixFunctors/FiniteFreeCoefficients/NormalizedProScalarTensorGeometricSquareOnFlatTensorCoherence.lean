/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.FiniteFreeCoefficients.Sites.FiniteFreeCoefficientExtensionData
public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.PreservesTotalTensorKFlatQuasiIsoSupplement
import WeilConjectures.SixFunctors.FiniteFreeCoefficients.ProUpperStarTensorCochainRepresentative
import WeilConjectures.SixFunctors.FiniteFreeCoefficients.ProScalarSheafPullbackMonoidal
import WeilConjectures.SixFunctors.FiniteFreeCoefficients.ProScalarPullbackCochainNormalization
import WeilConjectures.SixFunctors.FiniteFreeCoefficients.ProScalarPullNormalization
import all WeilConjectures.AlgebraicGeometry.Etale.Scalar.EtaleScalarPullbackTensorKFlat

/-! The cochain-level normalized pro-etale scalar/pullback tensor square.

Source: Stacks Tags 06YY, 07A4 and 0G7E; this is the pro-etale
specialization of the generic `normalized_cochain_square` calculation in
`EtaleScalarPullbackTensorKFlat`.
Proof in words: apply the generic normalized cochain square to the two pro-etale
sites. The site-specific inputs are the scalar representative transformation
and its tensor normalization (including invertibility on K-flat complexes), the
geometric representative and the upper-star tensor cochain representative, the
monoidal sheaf scalar/pullback isomorphism, and the defining mate equation for
`scalarPullbackProEtaleIso`. The resulting equality is evaluated at the two
K-flat representatives.
(blueprint: new-sf-normalized-pro-scalar-tensor-geometric-square-on-flat-tensor-law). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option Elab.async false
universe u
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.MonoidalClosed
open AlgebraicGeometry AlgebraicGeometry.Etale
open scoped CategoryTheory.Functor
namespace WeilConjectures.FiniteFreeCoefficients

private theorem kFlat_iff_total
    {C : Type*} [Category C] [Abelian C] [MonoidalCategory C]
    [MonoidalPreadditive C] [Limits.HasCountableCoproducts C]
    [∀ (U V W Z : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt U V W Z]
    [∀ (U V W : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor U V W]
    [∀ (U V W : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ U V W]
    (P : CochainComplex C ℤ) :
    (HomologicalComplex.quasiIso C (.up ℤ)).kFlat P ↔ P.IsKFlatForTotalTensor := Iff.rfl

/-- The normalized cochain square before inverse-oriented assembly.

This is the forward square obtained by the
generic normalized cochain-square argument after supplying the pro-etale
representative transformations, tensor normalization equations, upper-star
cochain comparison, monoidal sheaf pullback comparison, and scalar/pullback
mate equation.
Source: Stacks Tags 06YY, 07A4 and 0G7E.
Proof in words: specialize the generic normalized cochain square to the
pro-etale scalar-extension and upper-star functors, use the two
`TensorNormalizationAux` witnesses supplied by the hypotheses, and cancel the
invertible representative maps on the K-flat complexes.
(blueprint: new-sf-normalized-pro-scalar-tensor-geometric-square-on-flat-tensor-law). -/
theorem pro_scalar_pullback_tensor_cochain_square
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (X : Scheme.{u}) (μ : Sites.TensorComparison true φ X)
    (hμ : Sites.NormalizedTensor true φ X μ)
    (Y : Scheme.{u}) (e : Y ≅ X) (δ : Sites.TensorComparison true φ Y)
    (hδ : Sites.NormalizedTensor true φ Y δ)
    (P Q : CochainComplex
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)) ℤ)
    (hP : CochainComplex.IsKFlatForTotalTensor P)
    (hQ : CochainComplex.IsKFlatForTotalTensor Q) :
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
          (Sites.proScalarPull φ e.hom).hom.app (DerivedCategory.Q.obj Q)) := by
  let EY := finiteVerdierOrdinaryExtension (Scheme.ProEt.topology X) φ
  let EX := finiteVerdierOrdinaryExtension (Scheme.ProEt.topology Y) φ
  let FA := ProEtale.upperStar (ModuleCat.{u + 1} A) e.hom
  let FB := ProEtale.upperStar (ModuleCat.{u + 1} B) e.hom
  let SY := ProEtale.pbcFixedScalarExtension (Scheme.ProEt.topology X) φ
  let SX := ProEtale.pbcFixedScalarExtension (Scheme.ProEt.topology Y) φ
  let LA := Sites.proPull A e.hom
  let LB := Sites.proPull B e.hom
  let := (finiteVerdierOrdinaryAdjunction (Scheme.ProEt.topology X) φ).isLeftAdjoint
  let := (finiteVerdierOrdinaryAdjunction (Scheme.ProEt.topology Y) φ).isLeftAdjoint
  have hnμ : ExceptionalCoefficients.TensorNormalizationAux EY SY
      (finiteVerdierScalarRepresentative (Scheme.ProEt.topology X) φ) μ := by
    rcases hμ with ⟨τ, hτ, heq⟩
    have h : μ = τ := eq_of_heq heq
    cases h
    exact hτ
  have hnδ : ExceptionalCoefficients.TensorNormalizationAux EX SX
      (finiteVerdierScalarRepresentative (Scheme.ProEt.topology Y) φ) δ := by
    rcases hδ with ⟨τ, hτ, heq⟩
    have h : δ = τ := eq_of_heq heq
    cases h
    exact hτ
  obtain ⟨rY, hrY, hYiso⟩ := pro_scalar_representative_transformation φ X
  obtain ⟨rX, hrX, hXiso⟩ := pro_scalar_representative_transformation φ Y
  let rA := pro_geometric_representative A e.hom
  let rB := pro_geometric_representative B e.hom
  rw [proScalarPull_eq_scalarPullbackProEtaleIso]
  simp only [ProEtale.leftDerivedUpperStarTensorIso_hom]
  apply normalized_cochain_square EY FB FA EX SY LB LA SX rY rB rA rX
    (finiteVerdierScalarRepresentative (Scheme.ProEt.topology X) φ)
    (fun K ↦ rB.app K) (fun K ↦ rA.app K)
    (finiteVerdierScalarRepresentative (Scheme.ProEt.topology Y) φ)
    hrY (fun _ ↦ rfl) (fun _ ↦ rfl) hrX
    μ (ProEtale.leftDerivedUpperStarTensorComparison (ModuleCat.{u + 1} B) e.hom)
    (ProEtale.leftDerivedUpperStarTensorComparison (ModuleCat.{u + 1} A) e.hom) δ
    hnμ (pro_upperStar_tensor_cochain_representative B e.hom)
    (pro_upperStar_tensor_cochain_representative A e.hom) hnδ
    (ProEtale.scalarPullbackProEtaleIso φ e.hom)
    (pro_scalar_sheaf_pullback_iso φ e.hom) (pro_scalar_sheaf_pullback_complex_iso φ e.hom)
    rfl (pro_scalar_sheaf_pullback_monoidal φ e.hom)
    (fun K _ ↦ pro_scalar_pullback_cochain_normalization φ e.hom K)
    hYiso (pro_geometric_representative_isIso B e.hom)
    P Q ((kFlat_iff_total P).2 hP) ((kFlat_iff_total Q).2 hQ)


end WeilConjectures.FiniteFreeCoefficients
