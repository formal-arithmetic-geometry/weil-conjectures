/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q3
-/
module

public import Sheaf.Paper.IntegralStratifiedPerfectModels
public import Sheaf.Paper.IntrinsicCompletion
import all Sheaf.Paper.CechPerfectComplexModel
import all Sheaf.Paper.SfbPerfectModelComplexComparison
import all Sheaf.Paper.CompletedConstantCoefficientEquivalence
import all Sheaf.AlgebraicGeometry.IntegralCompletedConstantModelTransport
import Sheaf.Paper.CompletedKoszulConstantTransport

/-! # Perfect constant complexes in the intrinsic coefficient presentation -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.sfbSheafTensor_hasWeakSheafify
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite
open scoped ChangeOfRings
namespace AlgebraicGeometry.Scheme
namespace CechPerfectModel


private local instance standardDerived {C : Type (u + 1)} [SmallCategory C]
    {J : GrothendieckTopology C} (O : Sheaf J CommRingCat.{u + 1}) :
    HasDerivedCategory (ConstantCompletion.Mod O) := HasDerivedCategory.standard _

attribute [local irreducible] normalizedComparison comparisonModulesEquiv

private def normalizedRealization (T : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) :
    integralConstantModule T d ⋙ (comparisonModulesEquiv T d).functor ≅
      commutativeSiteConstantModuleFunctor (completedCechTopology T) A ⋙
        ConstantCompletion.change
          (ConstantCompletion.coefficientMap (completedCechTopology T) A d.ideal) := by
  let F := integralConstantModule T d
  let G := pbcRestrict (pbcCompletedComparison T d).hom
  let H := adicLisseConstantModules T A ⋙
    completedAdicChange T (CompletedConstantReduction.base T d.ideal)
  let S := toSmall ((adicLisseForget T).obj (adicLisseCompletedRing T d.ideal))
  let c := CechConstantAlgebra.completionIso T d.ideal
  let R := ConstantCompletion.res c.inv
  let M := commutativeSiteConstantModuleFunctor (completedCechTopology T) A ⋙
    ConstantCompletion.change
      (ConstantCompletion.coefficientMap (completedCechTopology T) A d.ideal)
  let e : H ⋙ S ≅ M ⋙ ConstantCompletion.res c.hom :=
    (Functor.associator _ _ _) ≪≫ cech_completedRealizationIso T A d.ideal ≪≫
      (Functor.associator _ _ _).symm
  exact Functor.isoWhiskerLeft F (normalizedComparison T d) ≪≫
    (Functor.associator F G (S ⋙ R)).symm ≪≫
    Functor.isoWhiskerRight (completedModelRoundTrip T d) (S ⋙ R) ≪≫
    (Functor.associator H S R).symm ≪≫ Functor.isoWhiskerRight e R ≪≫
    Functor.associator M (ConstantCompletion.res c.hom) R ≪≫
    Functor.isoWhiskerLeft M (scalarRestrictionEquivalence c).unitIso.symm ≪≫
    Functor.rightUnitor M

attribute [local irreducible] normalizedRealization cech_completedRealizationIso

private theorem realization_complete (T : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] [IsNoetherianRing A]
    (d : AdicCoefficientDatum A)
    (P : completedConstantDerived (ModuleCat.{u + 1} A))
    (hP : @DerivedCategory.IsPerfectRingComplex A _ (HasDerivedCategory.standard _) P) :
    ConstantCompletion.IsComplete
      (ConstantCompletion.projection (completedCechTopology T) A d.ideal 0)
      ((comparisonModulesEquiv T d).mapDerivedCategory.functor.obj
        ((integralConstantDerived T d).obj P)) := by
  obtain ⟨D, lo, hi, hlo, hhi, hterms, ⟨e⟩⟩ := hP
  let F := integralConstantModule T d
  let E := comparisonModulesEquiv T d
  let := (integralConstantModule_exact T d).1
  let := (integralConstantModule_exact T d).2
  let c : (E.functor.mapHomologicalComplex (.up ℤ)).obj
      ((F.mapHomologicalComplex (.up ℤ)).obj D) ≅
      AdicPerfectModel.model (completedCechTopology T) d.ideal D :=
    HomologicalComplex.Hom.isoOfComponents
      (fun q ↦ (normalizedRealization T d).app (D.X q))
      (by intro i j _; exact ((normalizedRealization T d).hom.naturality (D.d i j)).symm)
  let α := E.functor.mapDerivedCategory.mapIso (F.mapDerivedCategory.mapIso e) ≪≫
    E.functor.mapDerivedCategory.mapIso (F.mapDerivedCategoryFactors.app D) ≪≫
    E.functor.mapDerivedCategoryFactors.app _ ≪≫
    DerivedCategory.Q.mapIso c
  have hc := cech_model_complete T d.ideal D (fun q ↦ ⟨(hterms q).2, (hterms q).1⟩)
  intro U f hf
  exact (hc U f hf).of_iso
    ((derivedInternalHom ((completedCechTopology T).over U)
      ((ConstantCompletion.completed (completedCechTopology T) A d.ideal).over U)).mapIso
      ((Iso.refl _).prod ((ringedDerivedRestriction _ U).mapIso α)))

end CechPerfectModel

attribute [local instance] HasDerivedCategory.standard

/-- A perfect scalar complex has an invertible intrinsic completion unit after
completed constant realization.
Source: Bhatt--Scholze, Proposition 6.6.11, reverse implication and Lemma 6.5.8.
(blueprint: lem-weil-pbc-cech-perfect-model-completeness).

Proof: realize finite projectives as retracts of finite sums of the coefficient
unit. The inverse-limit coefficient unit is complete on every slice, by the
multiplication-difference criterion and exact countable products on the pro-etale
site. This criterion holds termwise for finite projective retracts and hence for
the realized complex. Compare constant sheafification and scalar extension on the
AsSmall site by their universal properties. The finite-projection coefficient
comparison fixes each scalar and therefore identifies the Koszul units. The
constant-completion reflector criterion makes the transported unit invertible;
the exact derived equivalence reflects this property. -/
theorem cechPerfectModel_intrinsicComplete (T : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] [IsNoetherianRing A]
    (d : AdicCoefficientDatum A)
    (P : completedConstantDerived (ModuleCat.{u + 1} A))
    (hP : @DerivedCategory.IsPerfectRingComplex A _ (HasDerivedCategory.standard _) P)
    (r : ℕ) (a : Fin r → A) (ha : Ideal.span (Set.range a) = d.ideal)
    (C : CochainComplex (pbcModules T (pbcAdicCompletion T d)) ℤ)
    (eC : DerivedCategory.Q.obj C ≅ (integralConstantDerived T d).obj P) :
    IsDerivedCompleteIntrinsic T d r a ha ((integralConstantDerived T d).obj P) C eC := by
  let β := CechConstantAlgebra.algebraIso T d.ideal (pbcCompletedComparison T d)
  let E := comparisonModulesEquiv T d
  let F := E.mapDerivedCategory.functor
  let R := ConstantCompletion.res β.inv
  let : PreservesFiniteLimits (ConstantCompletion.res β.inv) :=
    (siteRestrictScalars_exact β.inv).1
  let : PreservesFiniteColimits (ConstantCompletion.res β.inv) :=
    (siteRestrictScalars_exact β.inv).2
  let : (ConstantCompletion.res β.inv).Additive :=
    Functor.additive_of_preserves_binary_products _
  let : (completedCechModulesEquiv T d).functor.IsEquivalence :=
    (completedCechModulesEquiv T d).isEquivalence_functor
  have : (completedCechModulesEquiv T d).functor.Additive :=
    Functor.additive_of_preserves_binary_products _
  let : PreservesFiniteLimits
      ((completedCechModulesEquiv T d).functor ⋙ R) :=
    comp_preservesFiniteLimits _ _
  let : PreservesFiniteColimits
      ((completedCechModulesEquiv T d).functor ⋙ R) :=
    comp_preservesFiniteColimits _ _
  let H := (completedCechModulesEquiv T d).functor ⋙ R
  let σ : E.functor ≅ H := comparisonModulesEquiv_to_cech T d
  let : PreservesFiniteLimits H := preservesFiniteLimits_of_natIso σ
  let : PreservesFiniteColimits H := preservesFiniteColimits_of_natIso σ
  let δ : F ≅ (completedCechDerivedEquiv T d).functor ⋙ ConstantCompletion.dres β.inv :=
    Functor.mapDerivedCategoryNatIso σ ≪≫
      Functor.mapDerivedCategoryCompIso (completedCechModulesEquiv T d).functor R
  obtain ⟨c, hc⟩ := completed_koszul_constant_transport T d β
    (comparisonCompletedRingIso_scalar T d) F δ r a ha C
  have hcomplete := CechPerfectModel.realization_complete T d P hP
  have hC : ConstantCompletion.IsComplete
      (ConstantCompletion.projection (completedCechTopology T) A d.ideal 0)
      (F.obj (DerivedCategory.Q.obj C)) := by
    intro U f hf
    exact (hcomplete U f hf).of_iso
      ((derivedInternalHom ((completedCechTopology T).over U)
        ((ConstantCompletion.completed (completedCechTopology T) A d.ideal).over U)).mapIso
        ((Iso.refl _).prod ((ringedDerivedRestriction _ U).mapIso (F.mapIso eC))))
  obtain ⟨_, _, _, _, hiff⟩ := ConstantCompletion.koszul_quotient_reflector
    (completedCechTopology T) A d.ideal true r a ha
  have hu := (hiff (F.obj (DerivedCategory.Q.obj C))).mpr hC
  have hm : IsIso (F.map (DerivedCategory.Q.map
      (intrinsicCompletionComplexUnit T d r a C))) := by
    apply (isIso_comp_right_iff _ c.hom).mp
    rw [hc]
    exact hu
  have : IsIso (DerivedCategory.Q.map (intrinsicCompletionComplexUnit T d r a C)) :=
    (isIso_iff_of_reflects_iso _ F).mp hm
  unfold IsDerivedCompleteIntrinsic intrinsicCompletionUnit
  infer_instance

end AlgebraicGeometry.Scheme
