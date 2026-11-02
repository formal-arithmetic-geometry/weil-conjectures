/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Finite.Dualizing.FiniteDualizingData
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.RestrictScalars

/-! # Comparison-site transport core for finite dualizing restriction -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
variable (X : Scheme.{u})

-- The ordinary and derived square arguments follow the proved private helpers in
-- WeilConjectures.AlgebraicGeometry.Normalized.NormalizedOriginComparisonCoherence,
-- specialized here without changing its API.
open AlgebraicGeometry.ProEtale in
set_option backward.defeqAttrib.useBackward true in
private theorem fd_ordinaryRestrictionComp (T : Scheme.{u})
    {R S V : Type (u + 1)} [CommRing R] [CommRing S] [CommRing V]
    (φ : R →+* S) (ψ : S →+* V) (χ : R →+* V) (h : χ = ψ.comp φ) :
    (pbcComparisonRestrict T χ).hom ≫
      Functor.whiskerRight (Sheaf.restrictScalarsCompIso T.smallEtaleTopology φ ψ χ h).inv
        (comparisonUpperStar (ModuleCat.{u + 1} R) T) =
    Functor.whiskerLeft (comparisonUpperStar (ModuleCat.{u + 1} V) T)
        (Sheaf.restrictScalarsCompIso (Scheme.ProEt.topology T) φ ψ χ h).inv ≫
      (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight (pbcComparisonRestrict T ψ).hom
        (Sheaf.restrictScalars (Scheme.ProEt.topology T) φ) ≫
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft (Sheaf.restrictScalars T.smallEtaleTopology ψ)
        (pbcComparisonRestrict T φ).hom ≫ (Functor.associator _ _ _).inv := by
  let aR := comparisonAdjunction (ModuleCat.{u + 1} R) T
  let aS := comparisonAdjunction (ModuleCat.{u + 1} S) T
  let aV := comparisonAdjunction (ModuleCat.{u + 1} V) T
  let eφ := Sheaf.restrictCoextendScalarsAdj T.smallEtaleTopology φ
  let eψ := Sheaf.restrictCoextendScalarsAdj T.smallEtaleTopology ψ
  let eχ := Sheaf.restrictCoextendScalarsAdj T.smallEtaleTopology χ
  let pφ := Sheaf.restrictCoextendScalarsAdj (Scheme.ProEt.topology T) φ
  let pψ := Sheaf.restrictCoextendScalarsAdj (Scheme.ProEt.topology T) ψ
  let pχ := Sheaf.restrictCoextendScalarsAdj (Scheme.ProEt.topology T) χ
  apply (conjugateEquiv ((eψ.comp eφ).comp aR) (aV.comp pχ)).injective
  rw [← conjugateEquiv_comp _ (eχ.comp aR)]
  rw [← conjugateEquiv_comp _ (aV.comp (pψ.comp pφ))]
  rw [← conjugateEquiv_comp _ ((aV.comp pψ).comp pφ)]
  rw [← conjugateEquiv_comp _ ((eψ.comp aS).comp pφ)]
  rw [← conjugateEquiv_comp _ (eψ.comp (aS.comp pφ))]
  rw [← conjugateEquiv_comp _ (eψ.comp (eφ.comp aR))]
  have hc {U V : Type (u + 1)} [CommRing U] [CommRing V] (f : U →+* V) :
      conjugateEquiv
        ((Sheaf.restrictCoextendScalarsAdj T.smallEtaleTopology f).comp
          (comparisonAdjunction (ModuleCat.{u + 1} U) T))
        ((comparisonAdjunction (ModuleCat.{u + 1} V) T).comp
          (Sheaf.restrictCoextendScalarsAdj (Scheme.ProEt.topology T) f))
        (pbcComparisonRestrict T f).hom = 𝟙 _ := by
    change (conjugateEquiv _ _)
      ((conjugateEquiv _ _).symm (𝟙 _)) = _
    exact Equiv.apply_symm_apply _ _
  simp only [conjugateEquiv_whiskerRight, conjugateEquiv_whiskerLeft,
    conjugateEquiv_associator_hom, conjugateEquiv_associator_inv]
  dsimp only [aR, aS, aV, eφ, eψ, eχ, pφ, pψ, pχ]
  rw [hc, hc, hc]
  ext X : 2
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, NatTrans.id_app,
    Category.comp_id, Category.id_comp]
  ext U : 3
  rfl

open AlgebraicGeometry.ProEtale in
set_option backward.defeqAttrib.useBackward true in
private theorem fd_derivedRestrictionComp (T : Scheme.{u})
    {R S V : Type (u + 1)} [CommRing R] [CommRing S] [CommRing V]
    (φ : R →+* S) (ψ : S →+* V) (χ : R →+* V) (h : χ = ψ.comp φ)
    (K : DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} V))) :
    (pbcDerivedComparisonRestrict T χ).hom.app K ≫
      (comparisonUpperStar (ModuleCat.{u + 1} R) T).mapDerivedCategory.map
        ((Sheaf.derivedRestrictScalarsCompIso T.smallEtaleTopology h).inv.app K) =
    (Sheaf.derivedRestrictScalarsCompIso (Scheme.ProEt.topology T) h).inv.app
        ((comparisonUpperStar (ModuleCat.{u + 1} V) T).mapDerivedCategory.obj K) ≫
      (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology T) φ).map
        ((pbcDerivedComparisonRestrict T ψ).hom.app K) ≫
      (pbcDerivedComparisonRestrict T φ).hom.app
        ((Sheaf.derivedRestrictScalars T.smallEtaleTopology ψ).obj K) := by
  have ho (X : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} V)) :=
    congr_app (fd_ordinaryRestrictionComp T φ ψ χ h) X
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_inv_app, Functor.associator_hom_app,
    Category.comp_id, Category.id_comp] at ho
  have hd := Functor.mapDerivedCategorySquareIso_hom_app_comp
    (pbcComparisonRestrict T ψ) (pbcComparisonRestrict T φ)
    (pbcComparisonRestrict T χ)
    (Sheaf.restrictScalarsCompIso (Scheme.ProEt.topology T) φ ψ χ h).symm
    (Sheaf.restrictScalarsCompIso T.smallEtaleTopology φ ψ χ h).symm ho K
  exact hd

/--
The comparison-site part of the finite dualizing restriction transport.

Source: current blueprint, `lem-coef-finite-dualizing.proof.md`, final sentence;
this is the comparison pasting subdiagram before the final normalized restriction
component is appended.  The proof is the ordinary comparison restriction square
for the composite quotient, transported through exact derived localization and
then through the intrinsic restriction comparison.  The corresponding derived
square is obtained by the standard `mapDerivedCategorySquareIso` composition
lemma; naturality of the intrinsic restriction comparison gives the displayed
middle component.  This core is strictly simpler than the full transport because
it omits the final normalized restriction map, which is appended functorially in
the proof of the main theorem.
(blueprint: new-finitedualizing-restriction-transport-core)
-/
theorem finiteDualizingRealizationRestriction_transport_core
    {r m n : ℕ} (hrm : m ≤ r) (hmn : n ≤ m)
    (K : Etale.DerivedCategoryModule (finiteDualizingCoeff l E n) X) :
    (sfIntrinsicDerivedEquivalence X
      (Padic.coefficientExtensionRing l E (r + 1))).functor.map
        ((ProEtale.pbcDerivedComparisonRestrict X
          (finiteDualizingQuotient l E (hmn.trans hrm))).inv.app K) ≫
      (sfIntrinsicDerivedEquivalence X
        (Padic.coefficientExtensionRing l E (r + 1))).functor.map
        ((Sheaf.derivedRestrictScalarsCompIso (ProEt.topology X)
          (finiteDualizingQuotient_comp l E hrm hmn)).inv.app
          ((ProEtale.comparisonUpperStar
            (ModuleCat (finiteDualizingCoeff l E n)) X).mapDerivedCategory.obj K)) ≫
      (finiteDualizingIntrinsicRestriction l E X hrm).inv.app
        ((Sheaf.derivedRestrictScalars (ProEt.topology X)
          (finiteDualizingQuotient l E hmn)).obj
          ((ProEtale.comparisonUpperStar
            (ModuleCat (finiteDualizingCoeff l E n)) X).mapDerivedCategory.obj K)) =
    (sfIntrinsicDerivedEquivalence X
      (Padic.coefficientExtensionRing l E (r + 1))).functor.map
        ((ProEtale.comparisonUpperStar
          (ModuleCat (finiteDualizingCoeff l E r)) X).mapDerivedCategory.map
          ((Sheaf.derivedRestrictScalarsCompIso X.smallEtaleTopology
            (finiteDualizingQuotient_comp l E hrm hmn)).inv.app K)) ≫
      (sfIntrinsicDerivedEquivalence X
        (Padic.coefficientExtensionRing l E (r + 1))).functor.map
        ((ProEtale.pbcDerivedComparisonRestrict X
          (finiteDualizingQuotient l E hrm)).inv.app
          ((Sheaf.derivedRestrictScalars X.smallEtaleTopology
            (finiteDualizingQuotient l E hmn)).obj K)) ≫
      (finiteDualizingIntrinsicRestriction l E X hrm).inv.app
        ((ProEtale.comparisonUpperStar
          (ModuleCat (finiteDualizingCoeff l E m)) X).mapDerivedCategory.obj
          ((Sheaf.derivedRestrictScalars X.smallEtaleTopology
            (finiteDualizingQuotient l E hmn)).obj K)) ≫
      (normalizedDVRRes l E X hrm).map
        ((sfIntrinsicDerivedEquivalence X
          (Padic.coefficientExtensionRing l E (m + 1))).functor.map
          ((ProEtale.pbcDerivedComparisonRestrict X
            (finiteDualizingQuotient l E hmn)).inv.app K)) := by
  have hd := fd_derivedRestrictionComp X
    (finiteDualizingQuotient l E hrm) (finiteDualizingQuotient l E hmn)
    (finiteDualizingQuotient l E (hmn.trans hrm))
    (finiteDualizingQuotient_comp l E hrm hmn) K
  have hc :
      (ProEtale.pbcDerivedComparisonRestrict X
          (finiteDualizingQuotient l E (hmn.trans hrm))).inv.app K ≫
        (Sheaf.derivedRestrictScalarsCompIso (ProEt.topology X)
          (finiteDualizingQuotient_comp l E hrm hmn)).inv.app
          ((ProEtale.comparisonUpperStar
            (ModuleCat (finiteDualizingCoeff l E n)) X).mapDerivedCategory.obj K) =
      (ProEtale.comparisonUpperStar
          (ModuleCat (finiteDualizingCoeff l E r)) X).mapDerivedCategory.map
        ((Sheaf.derivedRestrictScalarsCompIso X.smallEtaleTopology
          (finiteDualizingQuotient_comp l E hrm hmn)).inv.app K) ≫
      (ProEtale.pbcDerivedComparisonRestrict X
          (finiteDualizingQuotient l E hrm)).inv.app
        ((Sheaf.derivedRestrictScalars X.smallEtaleTopology
          (finiteDualizingQuotient l E hmn)).obj K) ≫
      (Sheaf.derivedRestrictScalars (ProEt.topology X)
          (finiteDualizingQuotient l E hrm)).map
        ((ProEtale.pbcDerivedComparisonRestrict X
          (finiteDualizingQuotient l E hmn)).inv.app K) := by
    apply (cancel_epi ((ProEtale.pbcDerivedComparisonRestrict X
      (finiteDualizingQuotient l E (hmn.trans hrm))).hom.app K)).1
    rw [Iso.hom_inv_id_app_assoc]
    rw [← Category.assoc, ← Category.assoc, hd]
    simp only [Category.assoc, Iso.hom_inv_id_app]
    erw [Category.id_comp, ← Functor.map_comp, Iso.hom_inv_id_app,
      CategoryTheory.Functor.map_id, Category.comp_id]
  have hn := (finiteDualizingIntrinsicRestriction l E X hrm).inv.naturality
    ((ProEtale.pbcDerivedComparisonRestrict X
      (finiteDualizingQuotient l E hmn)).inv.app K)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hn
  have hmap := congrArg (fun f ↦
    (sfIntrinsicDerivedEquivalence X
      (Padic.coefficientExtensionRing l E (r + 1))).functor.map f ≫
      (finiteDualizingIntrinsicRestriction l E X hrm).inv.app
        ((Sheaf.derivedRestrictScalars (ProEt.topology X)
          (finiteDualizingQuotient l E hmn)).obj
          ((ProEtale.comparisonUpperStar
            (ModuleCat (finiteDualizingCoeff l E n)) X).mapDerivedCategory.obj K))) hc
  simp only [Functor.map_comp, Category.assoc] at hmap
  erw [hn] at hmap
  exact hmap

end WeilConjectures
