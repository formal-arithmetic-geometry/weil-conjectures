/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.CoefficientCompatibility.EtaleProEtaleCoefficientCompatibility
public import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactScalarCoherence
import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryChartSumBoundaryScalar
import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryChartSumScalarRepresentative
import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryChartNormalizationBoundary
import all WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactScalarCoherence
import all WeilConjectures.AlgebraicGeometry.Etale.Open.EtaleOpenTensor
import all WeilConjectures.AlgebraicGeometry.Scalar.ScalarPullbackIsoUniqueness

/-! # Unbounded scalar compatibility of graph-normalized etale compact support

Source: blueprint smooth-purity reduction, Charts.
(blueprint: lem-pur-ordinary-chart-sum-normalization).
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale
open AlgebraicGeometry.ProEtale.CoefficientCompatibility
set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2
attribute [local irreducible] Functor.leftAdjoint Functor.rightAdjoint
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor Functor.mapDerivedCategory
  upperStar lowerStar

/-- Unbounded scalar compatibility of graph-normalized etale compact support.
Source: blueprint smooth-purity reduction, Charts.
(blueprint: lem-pur-ordinary-chart-sum-normalization).

Proof: Represent the arbitrary derived input by a complex whose terms are flat and which is native
K-flat: take a K-flat homotopy representative and a termwise flat K-flat quasi-isomorphic
replacement.
On this representative paste the scalar graph-boundary square, the exact-derived sum
representative square and the two graph-normalization boundary equations. Identify the open
comparison by its prescribed inverse-unit normalization, and cancel the invertible scalar
representative.
Cancel the normalization isomorphisms to obtain the forward comparison square on the
representative. Naturality of both composite natural transformations transports the equation along
the representative isomorphism to the given derived object. -/
theorem ordinaryChartSumNormalization
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (f : X ⟶ Y) [Etale f] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f) (NA : EtaleCompactSupportNormalization A)
    (NB : EtaleCompactSupportNormalization B) (L : DerivedCategoryModule A X) :
    (compactScalarMap φ c).app L ≫
        (NB.comparison f c).hom.app ((scalarExtension φ X).obj L) =
      (scalarExtension φ Y).map ((NA.comparison f c).hom.app L) ≫
        (sumCoefficientIso φ f).hom.app L := by
  obtain ⟨H, hH, ⟨eH⟩⟩ := DerivedCategory.exists_kFlat_iso L
  obtain ⟨H, rfl⟩ := H.quotient_obj_surjective
  obtain ⟨P, π, hπ, hf, hP⟩ := CochainComplex.exists_quasiIso_flat_kFlat H
  have := hπ
  let eP := asIso (DerivedCategory.Q.map π) ≪≫ eH
  have := scalarRepresentative_isIso φ X P hP
  have hcalc := ordinaryChartSumBoundaryScalar φ f c P hP hf
  have hsum := ordinaryChartSumScalarRepresentative φ f P
  change (scalarExtension φ Y).map _ ≫ _ ≫ _ =
    (sumCoefficientIso φ f).hom.app (DerivedCategory.Q.obj P) ≫ _ ≫ _ at hsum
  have hNA := ordinaryChartNormalizationBoundary A NA f c P
  have hNB := ordinaryChartNormalizationBoundary B NB f c
    (coefficientExtendedComplex φ X P)
  have hmodel :
      (Etale.scalarExtension φ Y).map ((NA.comparison f c).inv.app
          (DerivedCategory.Q.obj P)) ≫ (compactScalarMap φ c).app (DerivedCategory.Q.obj P) =
        (sumCoefficientIso φ f).hom.app (DerivedCategory.Q.obj P) ≫
          (NB.comparison f c).inv.app
            ((Etale.scalarExtension φ X).obj (DerivedCategory.Q.obj P)) := by
    apply (cancel_mono ((Etale.rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} B) c).map (Etale.scalarExtensionRepresentative φ X P))).mp
    have h := congrArg (fun z ↦
      (Etale.scalarExtension φ Y).map
        ((Etale.etaleLowerShriek (ModuleCat.{u + 1} A) f
          inferInstance).mapDerivedCategoryFactors.hom.app
          P) ≫ z) hcalc
    dsimp only [compactScalarMap, ExceptionalCoefficients.compactSupportMap,
      properCoefficientMap] at *
    simp only [Category.assoc] at h ⊢
    rw [← Functor.map_comp_assoc, hNA] at h
    rw [reassoc_of% hsum, hNB] at h
    have hn := (NB.comparison f c).inv.naturality
      (Etale.scalarExtensionRepresentative φ X P)
    dsimp only [Functor.comp_map] at hn
    rw [hn] at h
    have hopen : (ExceptionalCoefficients.openIso φ c.i).hom.app
        (DerivedCategory.Q.obj P) =
        (properOpenCoefficientOpenIso φ c.i (DerivedCategory.Q.obj P)).hom := by
      have h : ((ExceptionalCoefficients.openIso φ c.i).app
          (DerivedCategory.Q.obj P)).symm =
          (properOpenCoefficientOpenIso φ c.i (DerivedCategory.Q.obj P)).symm := by
        apply Iso.ext
        exact compactScalarOpen_normalization φ c.i (DerivedCategory.Q.obj P)
      exact congrArg (fun e ↦ e.inv) h
    simpa only [hopen, compactScalarMap, Category.assoc,
      Etale.rightDerivedLowerShriekOfCompactification, Etale.rightDerivedLowerStar,
      Functor.comp_map] using h
  have hQP :
      (compactScalarMap φ c).app (DerivedCategory.Q.obj P) ≫
          (NB.comparison f c).hom.app
            ((Etale.scalarExtension φ X).obj (DerivedCategory.Q.obj P)) =
        (Etale.scalarExtension φ Y).map
            ((NA.comparison f c).hom.app (DerivedCategory.Q.obj P)) ≫
          (sumCoefficientIso φ f).hom.app (DerivedCategory.Q.obj P) := by
    apply (cancel_epi ((Etale.scalarExtension φ Y).map
      ((NA.comparison f c).inv.app (DerivedCategory.Q.obj P)))).mp
    simp only [← Category.assoc, hmodel]
    simp only [Category.assoc, Iso.inv_hom_id_app,
      ← Functor.map_comp_assoc, Iso.inv_hom_id_app,
      CategoryTheory.Functor.map_id, Category.id_comp]
    exact Category.comp_id _
  let α := Etale.compactScalarMap φ c ≫
    Functor.whiskerLeft (Etale.scalarExtension φ X) (NB.comparison f c).hom
  let β := Functor.whiskerRight (NA.comparison f c).hom (Etale.scalarExtension φ Y) ≫
    (sumCoefficientIso φ f).hom
  have hQP' : α.app (DerivedCategory.Q.obj P) = β.app (DerivedCategory.Q.obj P) := by
    simpa only [α, β, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app] using hQP
  have hL : α.app L = β.app L := by
    apply (cancel_epi
      ((Etale.rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} A) c ⋙ Etale.scalarExtension φ Y).map eP.hom)).mp
    rw [α.naturality eP.hom, β.naturality eP.hom, hQP']
  simpa only [α, β, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app] using hL

end AlgebraicGeometry.Etale
