/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V4
-/
module

public import Sheaf.Paper.CompletedConstantConstructibility
public import Sheaf.Paper.AdicStratifiedPerfect
public import Sheaf.AlgebraicGeometry.IntegralConstantCompletion

import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import Sheaf.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import Sheaf.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor
import Sheaf.CategoryTheory.RingedDerivedRestrictionGeneral
import Sheaf.Paper.IntegralCohomologicalAdicCriterionAdicBridge
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.RingTheory.Noetherian.Basic

/-!
# Integral completed coefficient local models

Source: Bhatt--Scholze, Proposition 6.8.11(3).
(blueprint: lem-sfb-integral-perfect-cohomology-completed-constant).
-/

@[expose] public noncomputable section

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

universe u c v

open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules
open scoped ChangeOfRings

namespace SheafOfModules
variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasSheafify J AddCommGrpCat.{u}]
  {R S : Sheaf J CommRingCat.{u}} (φ : R ⟶ S)
private def underlyingTensorIso
    (M : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :
    (changeOfRingsPresheaf.{v, c, u} φ M).presheaf ≅
      ((siteTensorRight
        ((restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).obj
          (unit.{v, c, u}
          ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S))).val).obj M.val).presheaf := by
  refine NatIso.ofComponents (fun V ↦ ?_) ?_
  · let : Module (R.obj.obj V) (S.obj.obj V) :=
      Module.compHom (S.obj.obj V) (φ.hom.app V).hom
    exact (TensorProduct.comm (R.obj.obj V) (S.obj.obj V) (M.val.obj V)).toAddEquiv.toAddCommGrpIso
  · intro V W f
    ext z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simpa only [map_add] using congrArg₂ (· + ·) ha hb
    | tmul s m =>
      change (TensorProduct.comm _ _ _) (changeOfRingsMap.{v, c, u} φ M f
        (s ⊗ₜ[R.obj.obj V, (φ.hom.app V).hom] m)) = _
      erw [(exists_changeOfRingsMap.{v, c, u} φ M f).choose_spec s m]
      rfl
variable (E : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) ⥤
    SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S))
  (h : ∀ M, E.obj M = changeOfRings.{v, c, u} φ M)
  (hm : ∀ {M N} (f : M ⟶ N), E.map f = eqToHom (h M) ≫
    changeOfRingsHom.{v, c, u} φ M f ≫ eqToHom (h N).symm)
set_option maxHeartbeats 400000 in
-- Comparing sheafification presentations expands the module structures.
private def scalarTensorComponent
    (M : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :
    (toSheaf.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S)).obj (E.obj M) ≅
      (presheafToSheaf J AddCommGrpCat.{u}).obj
        (((siteTensorRight
          ((restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).obj
            (unit.{v, c, u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S))).val).obj
              M.val).presheaf) := by
  let e₁ := (toSheaf.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S)).mapIso
    (eqToIso (h M))
  let e₂ := (PresheafOfModules.sheafificationCompToSheaf
    (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S).obj)).app
      (changeOfRingsPresheaf.{v, c, u} φ M)
  let e₃ := (presheafToSheaf J AddCommGrpCat.{u}).mapIso (underlyingTensorIso φ M)
  exact e₁ ≪≫ e₂ ≪≫ e₃
set_option maxHeartbeats 400000 in
-- Comparing sheafification presentations expands the module structures.
private def scalarTensorIso :
    E ⋙ toSheaf.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S) ≅
      siteSheafTensorRight.{v, c, u, u} (J := J) (A := R)
        ((restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).obj
          (unit.{v, c, u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S))) ⋙
            toSheaf.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) := by
  refine NatIso.ofComponents (scalarTensorComponent φ E h) ?_
  intro M N f
  dsimp only [scalarTensorComponent, Functor.comp_map, Iso.trans_hom,
    Functor.mapIso_hom, eqToIso.hom]
  rw [hm f]
  simp only [Functor.map_comp, Category.assoc]
  erw [← Functor.map_comp_assoc (toSheaf.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S))
    (eqToHom (h N).symm) (eqToHom (h N)), eqToHom_trans, eqToHom_refl,
    CategoryTheory.Functor.map_id, Category.id_comp]
  apply (cancel_epi ((toSheaf.{u} _).map (eqToHom (h M)))).mpr
  change (presheafToSheaf (J) AddCommGrpCat.{u}).map
    ((PresheafOfModules.toPresheaf
      (((sheafCompose J (forget₂ CommRingCat RingCat)).obj S).obj)).map
      (show changeOfRingsPresheaf.{v, c, u} φ M ⟶
        changeOfRingsPresheaf.{v, c, u} φ N from
      { app := fun V ↦ (ModuleCat.extendScalars (φ.hom.app V).hom).map (f.val.app V)
        naturality := changeOfRingsHom_naturality φ M f })) ≫ _ = _
  change (presheafToSheaf J AddCommGrpCat.{u}).map _ ≫
    (presheafToSheaf J AddCommGrpCat.{u}).map (underlyingTensorIso φ N).hom =
    (presheafToSheaf J AddCommGrpCat.{u}).map (underlyingTensorIso φ M).hom ≫
      (presheafToSheaf J AddCommGrpCat.{u}).map _
  rw [← Functor.map_comp, ← Functor.map_comp]
  apply (presheafToSheaf (J) AddCommGrpCat.{u}).congr_map
  ext V z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simpa only [map_add] using congrArg₂ (· + ·) ha hb
  | tmul s m => rfl
include h hm in
private theorem scalarExtensionExact
    (hf : IsFlatOnSite (C := C) (J := J) (R := R)
      ((restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).obj
        (unit.{v, c, u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S)))) :
    PreservesFiniteLimits (E) ∧
      PreservesFiniteColimits (E) := by
  let T := siteSheafTensorRight.{v, c, u, u} (J := J) (A := R)
    ((restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).obj
      (unit.{v, c, u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S)))
  let : PreservesFiniteLimits T := hf.1
  let : PreservesFiniteColimits T := hf.2
  have : PreservesFiniteColimits
      (toSheaf.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :=
    (CategoryTheory.moduleSheaves_colimits_forgetful _).2.2.1
  have : PreservesFiniteColimits
      (toSheaf.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S)) :=
    (CategoryTheory.moduleSheaves_colimits_forgetful _).2.2.1
  have : PreservesFiniteLimits
      (E ⋙ toSheaf.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S)) :=
    preservesFiniteLimits_of_natIso (scalarTensorIso φ E h hm).symm
  have : PreservesFiniteColimits
      (E ⋙ toSheaf.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S)) :=
    preservesFiniteColimits_of_natIso (scalarTensorIso φ E h hm).symm
  exact ⟨preservesFiniteLimits_of_reflects_of_preserves _ (toSheaf _),
    preservesFiniteColimits_of_reflects_of_preserves _ (toSheaf _)⟩
end SheafOfModules


namespace AlgebraicGeometry.Scheme

/-- Canonical coefficient-sized pro-etale sheafification instance.
Source: Stacks Tag 03DA (blueprint: lem-sfb-integral-perfect-cohomology-completed-constant). -/
instance (priority := 3000) integralPerfectCohomologyWEquals (X : Scheme.{u}) :
    (ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{u, u + 1,
    u + 1, u + 2, u + 1} (ProEt.topology X)

/-- Flatness of completed coefficients makes ordinary scalar extension exact.
Source: Stacks Tag 093M
(blueprint: lem-sfb-integral-perfect-cohomology-completed-constant). -/
theorem completedConstantChange_exact
    (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A] [IsNoetherianRing A] (I : Ideal A) :
    PreservesFiniteLimits (completedAdicChange X (CompletedConstantReduction.base X I)) ∧
      PreservesFiniteColimits (completedAdicChange X (CompletedConstantReduction.base X I)) := by
  exact SheafOfModules.scalarExtensionExact (C := X.ProEt) (J := ProEt.topology X)
    (CompletedConstantReduction.base X I)
    (completedAdicChange X (CompletedConstantReduction.base X I))
    ((completedAdicChangeData X _).choose_spec.choose)
    ((completedAdicChangeData X _).choose_spec.choose_spec.choose)
    (CompletedConstantReduction.completed_constant_sheaf_reduction X I).1
private def completedModelHomologyIso
    (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (P : CochainComplex (ModuleCat.{u + 1} A) ℤ) (q : ℤ) :
    ((DerivedCategory.homologyFunctor _ q).obj (sfbCompletedModel X I P)) ≅
      (completedAdicChange X (CompletedConstantReduction.base X I)).obj
        ((adicLisseConstantModules X A).obj (P.homology q)) := by
  let C := adicLisseConstantModules X A
  let E := completedAdicChange X (CompletedConstantReduction.base X I)
  have hC := commutativeSiteConstantModuleFunctor_exact (ProEt.topology X) A
  have : PreservesFiniteLimits C := hC.2.1
  have : PreservesFiniteColimits C := hC.2.2
  have hE := completedConstantChange_exact X I
  have : PreservesFiniteLimits E := hE.1
  have : PreservesFiniteColimits E := hE.2
  exact (DerivedCategory.homologyFunctorFactors _ q).app _ ≪≫
    ((((C.mapHomologicalComplex (.up ℤ)).obj P).sc q).mapHomologyIso E) ≪≫
      E.mapIso ((P.sc q).mapHomologyIso C)
private def identityExtensionIso (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (M : proEtaleRingModules X R) : changeOfRings.{u, u + 1, u + 1} (𝟙 R) M ≅ M := by
  let e : changeOfRingsPresheaf.{u, u + 1, u + 1} (𝟙 R) M ≅ M.val :=
    PresheafOfModules.isoMk (fun V ↦ (ModuleCat.extendScalarsId.{u + 1, u + 1} (R.obj.obj V)).app
      (M.val.obj V)) (by
        intro V W f
        apply ModuleCat.ExtendScalars.hom_ext
        intro m
        symm
        change M.val.map f ((ModuleCat.extendScalarsId.{u + 1, u + 1}
          (R.obj.obj V)).hom.app _ ((1 : R.obj.obj V) ⊗ₜ[R.obj.obj V, RingHom.id _] m)) = _
        rw [ModuleCat.extendScalarsId_hom_app_one_tmul]
        change M.val.map f m =
          (ModuleCat.extendScalarsId.{u + 1, u + 1} (R.obj.obj W)).hom.app _
            (changeOfRingsMap (𝟙 R) M f
              ((1 : R.obj.obj V) ⊗ₜ[R.obj.obj V, RingHom.id _] m))
        erw [(exists_changeOfRingsMap (𝟙 R) M f).choose_spec (1 : R.obj.obj V) m]
        simp only [map_one]
        rw [ModuleCat.extendScalarsId_hom_app_one_tmul])
  exact (PresheafOfModules.sheafification (𝟙 ((adicLisseForget X).obj R).obj)).mapIso e ≪≫
    (asIso (PresheafOfModules.sheafificationAdjunction
      (𝟙 ((adicLisseForget X).obj R).obj)).counit).app M
private def localHomologyIso {X S : Scheme.{u}} (i : S ⟶ X)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) (U : S.ProEt)
    (K : DerivedCategory (proEtaleRingModules X R)) (q : ℤ) :
    let R' := (adicLisseForget S).obj
      ((proEtaleSheafInverseImage i CommRingCat.{u + 1}).obj R)
    letI := HasDerivedCategory.standard (SheafOfModules.{u + 1} (R'.over U))
    (SheafOfModules.overFunctor _ U).obj
      ((proEtaleModuleInverseImage i R).obj ((DerivedCategory.homologyFunctor _ q).obj K)) ≅
    (DerivedCategory.homologyFunctor _ q).obj (sfbLocalRestriction i R U K) := by
  let R' := (adicLisseForget S).obj
    ((proEtaleSheafInverseImage i CommRingCat.{u + 1}).obj R)
  letI := HasDerivedCategory.standard (SheafOfModules.{u + 1} (R'.over U))
  let F := proEtaleRingModulePullback i R
    ((proEtaleSheafInverseImage i CommRingCat.{u + 1}).obj R) (Iso.refl _)
  let G := SheafOfModules.overFunctor.{u + 1} R' U
  have := (ringedOverFunctor_exactGeneral R' U).1
  have := (ringedOverFunctor_exactGeneral R' U).2.1
  have := (ringedOverFunctor_exactGeneral R' U).2.2
  let L := F.mapDerivedCategory.obj K
  let C := DerivedCategory.Q.objPreimage L
  exact G.mapIso (identityExtensionIso S _ _).symm ≪≫
    G.mapIso ((F.mapDerivedCategoryHomologyFunctorIso q).app K) ≪≫
    (G.mapDerivedCategoryHomologyFunctorIso q).app L ≪≫
    (DerivedCategory.homologyFunctor _ q).mapIso
      (G.mapDerivedCategory.mapIso (DerivedCategory.Q.objObjPreimageIso L).symm ≪≫
        G.mapDerivedCategoryFactors.app C)
private theorem finitePresentation_homology
    {A : Type (u + 1)} [CommRing A] [IsNoetherianRing A]
    (P : CochainComplex (ModuleCat.{u + 1} A) ℤ)
    (hP : ∀ q, Module.Finite A (P.X q)) (q : ℤ) :
    Module.FinitePresentation A (P.homology q) := by
  have := hP q
  have : Module.Finite A (P.cycles q) :=
    Module.Finite.of_injective (P.iCycles q).hom
      ((ModuleCat.mono_iff_injective _).1 inferInstance)
  have : Module.Finite A (P.homology q) :=
    Module.Finite.of_surjective (P.homologyπ q).hom
      ((ModuleCat.epi_iff_surjective _).1 inferInstance)
  exact Module.finitePresentation_of_finite A _

private theorem perfect_cohomology_of_model_comparison
    (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (hm : ∀ (P : CochainComplex (ModuleCat.{u + 1} A) ℤ) (q : ℤ),
      Nonempty (((DerivedCategory.homologyFunctor _ q).obj (sfbCompletedModel X I P)) ≅
        (completedAdicChange X (CompletedConstantReduction.base X I)).obj
          ((adicLisseConstantModules X A).obj (P.homology q))))
    (K : DerivedCategory (proEtaleRingModules X (adicLisseCompletedRing X I)))
    (hK : IsSfbStratifiedPerfect X I K) (q : ℤ) :
    IsCompletedConstantStratified X I ((DerivedCategory.homologyFunctor _ q).obj K) := by
  obtain ⟨s, hs, hK⟩ := hK
  let t : FiniteLocallyClosedStratification X :=
    { n := s.n
      stratum := s.stratum
      isLocallyClosed_stratum := s.isLocallyClosed_stratum
      iUnion_stratum_eq_univ := s.iUnion_stratum_eq_univ
      pairwise_disjoint_stratum := s.pairwise_disjoint_stratum
      domain := s.domain
      immersion := s.immersion
      isImmersion := s.isImmersion
      range_immersion := s.range_immersion }
  refine ⟨t, hs, ?_⟩
  intro a
  obtain ⟨V, hV, hK⟩ := hK a
  refine ⟨V, hV, ?_⟩
  intro U f hf
  obtain ⟨P, _, _, _, _, _, hP, ⟨e⟩⟩ := hK U f hf
  obtain ⟨ep⟩ := hm P q
  refine ⟨P.homology q, finitePresentation_homology P (fun i ↦ (hP i).2) q, ⟨?_⟩⟩
  let R' := (adicLisseForget (s.domain a)).obj
    ((proEtaleSheafInverseImage (s.immersion a) CommRingCat.{u + 1}).obj
      (adicLisseCompletedRing X I))
  letI := HasDerivedCategory.standard (SheafOfModules.{u + 1} (R'.over U))
  exact localHomologyIso (s.immersion a) _ U K q ≪≫
    (DerivedCategory.homologyFunctor _ q).mapIso e ≪≫
    (localHomologyIso (s.immersion a) _ U (sfbCompletedModel X I P) q).symm ≪≫
    (SheafOfModules.overFunctor _ U).mapIso
      ((proEtaleModuleInverseImage (s.immersion a) _).mapIso ep)

/-- Cohomology of a stratified perfect integral coefficient model is constructible
with finitely presented completed-constant local models.
Source: Bhatt--Scholze, Proposition 6.8.11(3), cohomology of perfect DVR complexes.
(blueprint: lem-sfb-integral-perfect-cohomology-completed-constant).
Proof: retain the finite constructible stratification and covering sieves of the perfect
model. For each coefficient complex P the kernel and image of every differential are finite,
since its terms are finite over the Noetherian DVR. Thus H^q(P) is finite and hence finitely
presented. Constant-module sheafification is exact and the completed coefficient ring is
flat over the constant ring, so realization commutes with cohomology. Module inverse image
along a stratum immersion and slice restriction are exact. Extension along the identity
coefficient map is canonically the identity, so these comparisons use the actual inverse-image
coefficient ring on both sides. Applying cohomology to the given local derived isomorphism
therefore identifies the restriction of H^q(K) with
the restriction of the completed constant module associated with H^q(P). These are the
witnesses of IsCompletedConstantStratified. This argument applies for each integer q and
also to the empty stratification of an empty scheme. -/
theorem integral_perfect_cohomology_completed_constant
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) [IsNoetherian X]
    (K : DerivedCategory (proEtaleRingModules X
      (adicLisseCompletedRing X (ProEtale.IntegralConstantCompletion.ideal l E))))
    (hK : IsSfbStratifiedPerfect X (ProEtale.IntegralConstantCompletion.ideal l E) K)
    (q : ℤ) :
    IsCompletedConstantStratified X (ProEtale.IntegralConstantCompletion.ideal l E)
      ((DerivedCategory.homologyFunctor _ q).obj K)  := by
  have := (integral_coefficient_hypotheses l E).1
  exact perfect_cohomology_of_model_comparison X _
    (fun P q ↦ ⟨completedModelHomologyIso X _ P q⟩) K hK q

end AlgebraicGeometry.Scheme
