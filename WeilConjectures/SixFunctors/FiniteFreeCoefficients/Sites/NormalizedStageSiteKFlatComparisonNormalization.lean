/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.FiniteFreeCoefficients.Sites.FiniteFreeCoefficientExtensionData
public import WeilConjectures.AlgebraicGeometry.SixFunctors.EvaluationHomSiteComparison
public import WeilConjectures.AlgebraicGeometry.Etale.Derived.EtaleDerivedScalarTensor
public import WeilConjectures.SixFunctors.FiniteFreeCoefficients.Sites.NormalizedStageSiteCochainTensorSquare

/-! # K-flat representatives for the normalized scalar/site comparison

Source: Stacks Project, Tag 0G7E, lemma-pullback-K-flat, together with Tags
06YS and 07A4 for representative and derived pullback normalizations.
(blueprint: lem-sf-normalized-stage-site-kflat-comparison-normalization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
universe u

open CategoryTheory AlgebraicGeometry MonoidalCategory
open WeilConjectures
open WeilConjectures.FiniteFreeCoefficients
namespace WeilConjectures.FiniteFreeCoefficients.Sites

/-- Flat-term K-flat preservation and representative normalization for the finite
scalar/site comparison.

Source: Stacks Project, Tag 0G7E, lemma-pullback-K-flat, together with Tags
06YS and 07A4.
(blueprint: lem-sf-normalized-stage-site-kflat-comparison-normalization).

Proof: the ringed-topos pullback theorem preserves flat terms and K-flatness for
both the comparison inverse image and scalar extension.  On a flat-term K-flat
complex the derived scalar/site mate is the localization of the ordinary mate,
with the displayed representative map.  Applying the same representative
normalization to two complexes and using the signed total tensor comparison
identifies each component of the derived scalar/site square with its cochain
component. Composing the four conjugated localization formulas gives each of the
two asserted composite-localization formulas. The ordinary cochain square then
gives equality of their localizations.
The assertions include arbitrary finite commutative rings, identity maps and
zero or empty complexes. -/
theorem normalized_stage_site_kflat_comparison_normalization
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (X : Scheme.{u})
    (μet : TensorComparison false φ X) (μpro : TensorComparison true φ X)
    (_hμet : NormalizedTensor false φ X μet)
    (_hμpro : NormalizedTensor true φ X μpro) :
    let FA := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X
    let FB := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} B) X
    let E := ProEtale.etaleSheafExtendScalars φ X
    let G := ProEtale.sheafExtendScalars φ X
    let fA := FA.mapHomologicalComplex (.up ℤ)
    let fB := FB.mapHomologicalComplex (.up ℤ)
    let e := E.mapHomologicalComplex (.up ℤ)
    let g := G.mapHomologicalComplex (.up ℤ)
    let q := DerivedCategory.Q (C := Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))
    let rEt := Etale.scalarExtensionRepresentative φ X
    let rPro := finiteVerdierScalarRepresentative (Scheme.ProEt.topology X) φ
    let cA := FA.mapDerivedCategoryFactors.hom
    let cB := FB.mapDerivedCategoryFactors.hom
    let r := fun K ↦ (scalar true φ X).map (cA.app K) ≫ rPro (fA.obj K)
    let d := fun K ↦ (nu B X).map (rEt K) ≫ cB.app (e.obj K)
    (∀ K : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ,
      (∀ n : ℤ, ObjectProperty.flat (K.X n)) →
      (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat K →
      (∀ n : ℤ, ObjectProperty.flat ((fA.obj K).X n)) ∧
      (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat (fA.obj K) ∧
      (∀ n : ℤ, ObjectProperty.flat ((e.obj K).X n)) ∧
      (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat (e.obj K) ∧
      (∀ n : ℤ, ObjectProperty.flat ((g.obj (fA.obj K)).X n)) ∧
      (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat (g.obj (fA.obj K)) ∧
      (∀ n : ℤ, ObjectProperty.flat ((fB.obj (e.obj K)).X n)) ∧
      (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat (fB.obj (e.obj K)) ∧
      IsIso (cA.app K) ∧ IsIso (rEt K) ∧ IsIso (r K) ∧ IsIso (d K) ∧
      (scalarSite φ X).hom.app (q.obj K) ≫ d K =
        r K ≫ DerivedCategory.Q.map (scalarSiteCochain φ X K)) ∧
    (∀ P Q : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ,
      (∀ n : ℤ, ObjectProperty.flat (P.X n)) →
      (∀ n : ℤ, ObjectProperty.flat (Q.X n)) →
      (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P →
      (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat Q →
      let τA := (ProEtale.siteComparisonTensorIso (ModuleCat.{u + 1} A) X
        (q.obj P)).hom.app (q.obj Q)
      let τB := (ProEtale.siteComparisonTensorIso (ModuleCat.{u + 1} B) X
        ((scalar false φ X).obj (q.obj P))).hom.app
          ((scalar false φ X).obj (q.obj Q))
      let μE := μet.hom.app (q.obj P, q.obj Q)
      let μG := μpro.hom.app ((nu A X).obj (q.obj P), (nu A X).obj (q.obj Q))
      let source := (scalar true φ X).map
        ((nu A X).map (Functor.LaxMonoidal.μ DerivedCategory.Q P Q)) ≫ r (P ⊗ Q)
      let target := (d P ⊗ₘ d Q) ≫
        Functor.LaxMonoidal.μ DerivedCategory.Q (fB.obj (e.obj P)) (fB.obj (e.obj Q))
      let left := (scalar true φ X).map τA ≫ μG ≫
        ((scalarSite φ X).hom.app (q.obj P) ⊗ₘ (scalarSite φ X).hom.app (q.obj Q))
      let right := (scalarSite φ X).hom.app (q.obj P ⊗ q.obj Q) ≫
        (nu B X).map μE ≫ τB
      IsIso source ∧ IsIso target ∧
      IsIso (Functor.LaxMonoidal.μ DerivedCategory.Q P Q) ∧
      μE ≫ (rEt P ⊗ₘ rEt Q) ≫ Functor.LaxMonoidal.μ DerivedCategory.Q (e.obj P) (e.obj Q) =
        (scalar false φ X).map (Functor.LaxMonoidal.μ DerivedCategory.Q P Q) ≫ rEt (P ⊗ Q) ≫
          DerivedCategory.Q.map (etaleScalarTensorCochain φ X P Q) ∧
      μG ≫ (r P ⊗ₘ r Q) ≫
          Functor.LaxMonoidal.μ DerivedCategory.Q (g.obj (fA.obj P)) (g.obj (fA.obj Q)) =
        (scalar true φ X).map ((cA.app P ⊗ₘ cA.app Q) ≫
          Functor.LaxMonoidal.μ DerivedCategory.Q (fA.obj P) (fA.obj Q)) ≫
          rPro (fA.obj P ⊗ fA.obj Q) ≫
          DerivedCategory.Q.map (proEtaleScalarTensorCochain φ X (fA.obj P) (fA.obj Q)) ∧
      τA ≫ (cA.app P ⊗ₘ cA.app Q) ≫
          Functor.LaxMonoidal.μ DerivedCategory.Q (fA.obj P) (fA.obj Q) =
        (nu A X).map (Functor.LaxMonoidal.μ DerivedCategory.Q P Q) ≫ cA.app (P ⊗ Q) ≫
          DerivedCategory.Q.map (siteTensorCochain A X P Q) ∧
      τB ≫ target =
        (nu B X).map ((rEt P ⊗ₘ rEt Q) ≫
          Functor.LaxMonoidal.μ DerivedCategory.Q (e.obj P) (e.obj Q)) ≫
          cB.app (e.obj P ⊗ e.obj Q) ≫
          DerivedCategory.Q.map (siteTensorCochain B X (e.obj P) (e.obj Q)) ∧
      left ≫ target = source ≫ DerivedCategory.Q.map
        (g.map (siteTensorCochain A X P Q) ≫
          proEtaleScalarTensorCochain φ X (fA.obj P) (fA.obj Q) ≫
          (scalarSiteCochain φ X P ⊗ₘ scalarSiteCochain φ X Q)) ∧
      right ≫ target = source ≫ DerivedCategory.Q.map
        (scalarSiteCochain φ X (P ⊗ Q) ≫
          fB.map (etaleScalarTensorCochain φ X P Q) ≫
          siteTensorCochain B X (e.obj P) (e.obj Q))) := by
  sorry

end WeilConjectures.FiniteFreeCoefficients.Sites
