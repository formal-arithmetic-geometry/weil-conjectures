/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H3
-/
module

public import Sheaf.CategoryTheory.RingedSiteCompleteElement
import Sheaf.Paper.RingedLocalizationRHomCalculus
import Sheaf.CategoryTheory.RingedSiteLocalizationFractionComparison
import Sheaf.Algebra.Homology.KInjectiveHomComplex
import Sheaf.Algebra.Homology.HomTensorTotal
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle

/-! Multiplicative stability of the localization-Hom vanishing criterion. -/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Pretriangulated.Opposite
open ZeroObject

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

namespace CategoryTheory

/-- Multiplying a complete element by any section preserves completeness.

Source: Stacks Project, algebraization.tex, Tags 0998 and 0996.
(blueprint: lem-weil-pbc-ringed-complete-element-mul).

Proof: On the slice over U, tensoring the coefficient localizations at a and f
identifies their tensor product with localization at af. Both coefficient modules
are flat. Derived tensor-Hom currying therefore identifies RHom(O[1/(af)], K|U)
with RHom(O[1/a], RHom(O[1/f], K|U)). The inner derived Hom vanishes by the
hypothesis. The outer functor preserves zero objects, since derived internal Hom
is triangulated in its second argument. This proves the result for arbitrary a,
including a = 0, and uses no boundedness of K. Identify the sequential-colimit
coefficient localization with the sheafified fraction localization by sending a
section x at stage n to x/f^n; the fraction relation gives the inverse colimit map.
-/
theorem ringedSite_complete_element_mul
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (R : Sheaf J CommRingCat.{u})
    [HasDerivedCategory.{w} (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))]
    [∀ U : C, HasDerivedCategory.{w} (SheafOfModules.{u}
      (((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).over U))]
    (K : DerivedCategory (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))) (U : C) (a f : R.obj.obj (op U))
    (hf : IsRingedSiteCompleteElement J R K U f) :
    IsRingedSiteCompleteElement J R K U (a * f) := by
  let R₀ := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R
  let : HasDerivedCategory.{w} (SheafOfModules.{u}
      ((sheafCompose (J.over U) (forget₂ CommRingCat RingCat)).obj (R.over U))) :=
    inferInstanceAs (HasDerivedCategory.{w} (SheafOfModules.{u} (R₀.over U)))
  let S := R.over U
  let A := SheafOfModules.{u}
    ((sheafCompose (J.over U) (forget₂ CommRingCat RingCat)).obj S)
  let : IsGrothendieckAbelian.{u} A := SheafOfModules.isGrothendieckAbelian _
  let := SheafOfModules.monoidalCategory S
  have := (SheafOfModules.tensorClosed S).1.some
  let M := ringedSiteDerivedRestriction R₀ U K
  let D := derivedInternalHom (J.over U) S
  let single := HomologicalComplex.single A (.up ℤ) 0
  let Qs := DerivedCategory.singleFunctor A 0
  let L := fun t : R.obj.obj (op U) ↦ localizationSliceCoefficient R U t
  let P := DerivedCategory.Q.objPreimage M
  let I := (CochainComplex.kInjectiveResolutionFunctor.{u} A).obj P
  have : I.IsKInjective := CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj.{u} A P
  let η := (CochainComplex.toKInjectiveResolution.{u} A).app P
  have : QuasiIso η := (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{u} A P).2
  have : IsIso (DerivedCategory.Q.map η) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ η).mpr inferInstance
  let eI : DerivedCategory.Q.obj I ≅ M :=
    (asIso (DerivedCategory.Q.map η)).symm ≪≫ DerivedCategory.Q.objObjPreimageIso M
  obtain ⟨ef⟩ := ringedSite_localization_fraction_comparison J R U f
  obtain ⟨eaf⟩ := ringedSite_localization_fraction_comparison J R U (a * f)
  have hF : IsZero (D.obj (op (Qs.obj (L f)), M)) :=
    hf.of_iso (D.mapIso ((Qs.mapIso ef).op.prod (Iso.refl M)))
  have hzero : IsBoundedLocalizationComplex R (0 : CochainComplex (localizationModules R) ℤ) := by
    have hz (n : ℤ) : IsZero ((0 : CochainComplex (localizationModules R) ℤ).X n) :=
      (HomologicalComplex.eval _ _ n).map_isZero (isZero_zero _)
    constructor
    · exact ⟨0, 0, fun n _ ↦ hz n⟩
    · intro n
      refine ⟨0, Fin.elim0, ?_⟩
      refine ⟨(hz n).iso ?_⟩
      apply (IsZero.iff_id_eq_zero _).mpr
      apply Sigma.hom_ext
      intro j
      exact Fin.elim0 j
  have hflat : CochainComplex.IsAcyclicTensorKFlat (R := S) (single.obj (L f)) :=
    (ringedLocalization_kflat_models R 0 hzero U f).2.1
  have : (homComplex (R := S) (single.obj (L f)) I).IsKInjective :=
    CochainComplex.isKInjective_homComplex_of_isKFlat _ _ hflat
  obtain ⟨einner⟩ := derivedInternalHom_obj_iso (J.over U) S
    (Qs.obj (L f)) M (single.obj (L f)) I
    ((DerivedCategory.singleFunctorIsoCompQ A 0).app _).symm eI
  have hinner : IsZero (DerivedCategory.Q.obj (homComplex (R := S) (single.obj (L f)) I)) :=
    hF.of_iso einner.symm
  obtain ⟨shift, hexact⟩ := (ringedInternalHom_exact (J.over U) S).1 (Qs.obj (L a))
  let := shift
  have := hexact
  have houter := ((Functor.curry.obj D).obj (op (Qs.obj (L a)))).map_isZero hinner
  obtain ⟨eouter⟩ := derivedInternalHom_obj_iso (J.over U) S
    (Qs.obj (L a)) _ (single.obj (L a)) (homComplex (R := S) (single.obj (L f)) I)
    ((DerivedCategory.singleFunctorIsoCompQ A 0).app _).symm (Iso.refl _)
  have hh := houter.of_iso eouter.symm
  obtain ⟨curry, _⟩ := homComplex_tensorTotal_iso S
  have htensor := hh.of_iso (DerivedCategory.Q.mapIso
    (curry (single.obj (L a)) (single.obj (L f)) I)).symm
  obtain ⟨eprod⟩ := ringedLocalization_tensor_product R U a f
  let T := CochainComplex.mapBifunctor (single.obj (L a)) (single.obj (L f))
    (MonoidalCategory.curriedTensor A)
  let eT : T ≅ single.obj (L (a * f)) :=
    CochainComplex.mapBifunctorSingle₁Iso (MonoidalCategory.curriedTensor A) (L a)
      (single.obj (L f)) ≪≫
      (HomologicalComplex.singleMapHomologicalComplex
        ((MonoidalCategory.curriedTensor A).obj (L a)) (.up ℤ) 0).app (L f) ≪≫
      single.mapIso eprod
  obtain ⟨efinal⟩ := derivedInternalHom_obj_iso (J.over U) S
    (Qs.obj (L (a * f))) M T I
    (DerivedCategory.Q.mapIso eT ≪≫
      ((DerivedCategory.singleFunctorIsoCompQ A 0).app _).symm) eI
  have hfinal := htensor.of_iso efinal
  exact hfinal.of_iso (D.mapIso ((Qs.mapIso eaf).symm.op.prod (Iso.refl M)))

end CategoryTheory
