/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F6
-/
module

public import Sheaf.Paper.LisseLocalizationData
import Sheaf.Paper.LisseLocalizationExistence
import Sheaf.Paper.LisseLocalizationSlices
import Sheaf.Paper.LisseLocalizationLocalFreeness
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.CategoryTheory.HomCongr
import Sheaf.Algebra.Category.ModuleCat.Sheaf.LocalizedSiteTensorRestriction

/-! # Exact localization and slice restriction of rational lisse objects

Source: Bhatt--Scholze, Lemma 6.8.2, Definitions 6.8.3 and 6.8.8,
Proposition 6.8.14(2); Stacks Tags 04IX, 03EL, 0941 and 06XS.
(blueprint: lem-tw-lisse-localization-restriction).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
universe u c v r w
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped TensorProduct ChangeOfRings
open SheafOfModules WeilConjectures.LisseLocalizationInterfaces
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
namespace WeilConjectures.LisseLocalization

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private theorem heart_image_single (X : Scheme.{u})
    [∀ x : X, Invertible (l : X.residueField x)]
    (dx : LocalizationData l E X) (K : sfRationalConstructibleCategory l E X)
    (hK : rationalLisseHeartProperty l E X K) :
    Nonempty (dx.realization.obj K ≅
      (DerivedCategory.singleFunctor (Modules X (rationalRing l E X)) 0).obj
        ((DerivedCategory.homologyFunctor (Modules X (rationalRing l E X)) 0).obj
          (dx.realization.obj K))) := by
  let A := Modules X (rationalRing l E X)
  let Y := dx.realization.obj K
  have : Y.IsGE 0 := (DerivedCategory.isGE_iff Y 0).2
    (fun i hi ↦ dx.halves false 0 K hK.1.2 i hi)
  have : Y.IsLE 0 := (DerivedCategory.isLE_iff Y 0).2
    (fun i hi ↦ dx.halves true 0 K hK.1.1 i hi)
  obtain ⟨M, ⟨e⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE Y 0
  let h : (DerivedCategory.homologyFunctor A 0).obj Y ≅ M :=
    (DerivedCategory.homologyFunctor A 0).mapIso e ≪≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso A 0).app M
  exact ⟨e ≪≫ (DerivedCategory.singleFunctor A 0).mapIso h.symm⟩

/-- Exact localization, all slice comparisons, and the degree-zero lisse realization.

Source: Bhatt--Scholze, Lemma 6.8.2, Definitions 6.8.3 and 6.8.8,
Proposition 6.8.14(2); Stacks 04IX, 03EL, 0941 and 06XS
(blueprint: lem-tw-lisse-localization-restriction).

Proof:
1. Apply lem-per-rational-continuous-coefficient-derived-localization to B_X and t.
Its constant R-action is the compatible constant quotient action. Exact ordinary
localization gives the normalized comparison with termwise derived localization,
all unbounded cohomology comparisons, and raw fraction descent.
2. Each localized half has its own integral representative. Exact localization
kills its forbidden cohomology, and realization preserves the chosen rational
isomorphism. Use both representatives for a heart object; no integral heart
lattice is assumed.
3. Apply lem-weil-proetale-weakly-etale-localization and
lem-tw-completed-coefficient-ringed-coherence to every site object. The residue
comparisons preserve constants and projections, so identify the inverse limits.
Localizing gives the rational comparison with b/t^n sent to the same fraction,
and identifies the localization units.
4. Restriction is exact (lem-weil-pbc-finite-type-restriction-exact). The
pure-tensor-normalized comparison of lem-sfb-localized-site-tensor-restriction
commutes with differentials, so descends to the F comparison by exact derived
factorization. It preserves scalar fractions on raw rational morphisms.
5. Apply lem-sp-slice-restriction-strict-derived-limit. Its K-injective strict
model supplies total right derived limits, the canonical compatible-tuple
comparison, and every normalized projection. The strict-tower homotopy-limit
lemma identifies these with the recorded IsDerivedLimit realization.
6. Completed chart pullback is the strict derived limit of finite pullbacks of
reductions. By lem-sfb-proetale-object-inverse-image-restriction these are literal
slice restrictions. The ringed derived tensor comparison identifies their tower
with the reduction tower of the restriction. Derived completeness, step 5 and
uniqueness in lem-weil-derived-limit-existence identify completed pullback with
restriction. None of these steps requires a finite-type chart.
7. A heart image is its H^0 in degree zero (lem-sf-derived-concentrated-single).
The defining lisse chart isomorphisms and steps 4--6 identify it locally with
A_U^r: a tensor (b_i) maps to (ab_i), with inverse given by the finite basis sum.
This allows r=0 and varying ranks. The rank-one calculation sends the unit to A[0].
8. Conjugate by the degree-zero identifications and use full faithfulness of
DerivedCategory.singleFunctor in degree zero (lem-weil-pbc-derived-single-fully-faithful).
This identifies the Hom sets by the displayed ordinary single-map formula. -/
theorem exists_lisseLocalizationRestriction (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))] :
    letI (x : X) : Invertible (l : X.residueField x) :=
      IsUnit.invertible (by
        let φ : D.k →+* X.residueField x :=
          (Scheme.Spec.preimage
            (X.fromSpecResidueField x ≫ (X ↘ Spec (.of D.k)))).unop.hom
        simpa only [map_natCast] using (finiteFieldDatumPrimeUnit D l hl).map φ)
    ∃ (dx : LocalizationData l E X)
      (du : ∀ U : X.ProEt, LocalizationData l E U.left),
      (∀ U : X.ProEt, ∃ c : SliceCoefficients l E U,
        Nonempty (SliceLocalization l E dx U (du U) c) ∧
        SliceLimitCompatibility U (X.adicLisseForget.obj (integralRing l E X)) ∧
        SliceTensorCompatibility (integralRing l E X) U ∧
        SliceTensorCompatibility (rationalRing l E X) U) ∧
      (∀ K : sfRationalConstructibleCategory l E X,
        rationalLisseHeartProperty l E X K →
          Nonempty (dx.realization.obj K ≅
            (DerivedCategory.singleFunctor (Modules X (rationalRing l E X)) 0).obj
              ((DerivedCategory.homologyFunctor (Modules X (rationalRing l E X)) 0).obj
                (dx.realization.obj K))) ∧
          SheafOfModules.IsFiniteLocallyFree
            ((DerivedCategory.homologyFunctor (Modules X (rationalRing l E X)) 0).obj
              (dx.realization.obj K))) ∧
      Nonempty (dx.realization.obj (pullbackTensorRationalUnit l E X) ≅
        (DerivedCategory.singleFunctor (Modules X (rationalRing l E X)) 0).obj
          (SheafOfModules.unit (X.adicLisseForget.obj (rationalRing l E X)))) ∧
      ∀ K L : sfRationalConstructibleCategory l E X,
        rationalLisseHeartProperty l E X K → rationalLisseHeartProperty l E X L →
          ∃ (eK : dx.realization.obj K ≅
              (DerivedCategory.singleFunctor (Modules X (rationalRing l E X)) 0).obj
                ((DerivedCategory.homologyFunctor (Modules X (rationalRing l E X)) 0).obj
                  (dx.realization.obj K)))
            (eL : dx.realization.obj L ≅
              (DerivedCategory.singleFunctor (Modules X (rationalRing l E X)) 0).obj
                ((DerivedCategory.homologyFunctor (Modules X (rationalRing l E X)) 0).obj
                  (dx.realization.obj L))),
            Function.Bijective (fun f ↦ eK.hom ≫
              (DerivedCategory.singleFunctor (Modules X (rationalRing l E X)) 0).map f ≫
                eL.inv) := by
  classical
  let (x : X) : Invertible (l : X.residueField x) :=
    IsUnit.invertible (by
      let φ : D.k →+* X.residueField x :=
        (Scheme.Spec.preimage
          (X.fromSpecResidueField x ≫ (X ↘ Spec (.of D.k)))).unop.hom
      simpa only [map_natCast] using (finiteFieldDatumPrimeUnit D l hl).map φ)
  obtain ⟨dx⟩ := nonempty_localizationData l E X
  have hdu (U : X.ProEt) := nonempty_localizationData l E U.left
  let du : ∀ U : X.ProEt, LocalizationData l E U.left := fun U ↦ (hdu U).some
  have hs (U : X.ProEt) : ∃ c : SliceCoefficients l E U,
      Nonempty (SliceLocalization l E dx U (du U) c) ∧
      SliceLimitCompatibility U (X.adicLisseForget.obj (integralRing l E X)) ∧
      SliceTensorCompatibility (integralRing l E X) U ∧
      SliceTensorCompatibility (rationalRing l E X) U := by
    obtain ⟨c, hc, hlim⟩ := localization_slice l E dx U (du U)
    exact ⟨c, hc, hlim,
      exists_localizedSiteTensorRestriction (ProEt.topology X) (integralRing l E X) U,
      exists_localizedSiteTensorRestriction (ProEt.topology X) (rationalRing l E X) U⟩
  obtain ⟨hfree, hunit⟩ := localization_localFreeness l E X dx du hs
  refine ⟨dx, du, hs, ?_, hunit, ?_⟩
  · intro K hK
    exact ⟨heart_image_single l E X dx K hK, hfree K hK⟩
  · intro K L hK hL
    obtain ⟨eK⟩ := heart_image_single l E X dx K hK
    obtain ⟨eL⟩ := heart_image_single l E X dx L hL
    refine ⟨eK, eL, ?_⟩
    exact ((Iso.homCongr eK.symm eL.symm).bijective).comp
      ((Functor.FullyFaithful.ofFullyFaithful
        (DerivedCategory.singleFunctor (Modules X (rationalRing l E X)) 0)).map_bijective _ _)

end WeilConjectures.LisseLocalization
