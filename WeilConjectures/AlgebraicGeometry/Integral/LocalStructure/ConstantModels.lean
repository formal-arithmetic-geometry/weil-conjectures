/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.Integral.LocalStructure.PullbackComparison
public import WeilConjectures.AlgebraicGeometry.AdicStratifiedPerfectData
public import WeilConjectures.AlgebraicGeometry.ContinuousScalarFinitePresentation
public import WeilConjectures.WeilObject.Sheaf.Stalk
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedPointModuleComparison
import all WeilConjectures.AlgebraicGeometry.IntegralSectionRegularScalars
import all WeilConjectures.AlgebraicGeometry.IntegralSectionScalarModels
import all WeilConjectures.AlgebraicGeometry.IntegralCompletedConstantModelTransport
import all WeilConjectures.AlgebraicGeometry.ContinuousScalarFinitePresentation

/-! # Inverse images of completed constant models of finite free complexes

A bounded complex of finite free scalar modules has two realizations on a scheme: the
completed constant model of the adic constructibility theory, and the pullback from the point
of the corresponding complex of free condensed modules. After inverse image along a morphism
of schemes they agree, through the equivalence of `exists_derived_integralRealization_pullback`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale
attribute [local irreducible] upperStarFromPoint CondensedRing.upperStar
  integralSectionFunctor Scheme.integralDetailedCoefficientComparison
  Scheme.proEtaleModuleInverseImage Scheme.integralConstantModule continuousScalarFunctor
attribute [local instance 2000] Scheme.proEtaleRingModules_hasDerivedCategory

/-- Additive functors which agree, compatibly with scalars, on the regular module agree on
complexes of finite free scalar modules.
(auxiliary; not a blueprint node). -/
theorem nonempty_mapHomologicalComplex_iso_of_freeScalars {A : Type u} [CommRing A]
    {C : Type*} [Category* C] [Abelian C]
    (F G : ModuleCat.{u + 1} A ⥤ C) [F.Additive] [G.Additive]
    [PreservesFiniteColimits F] [PreservesFiniteColimits G]
    (e : F.obj (ModuleCat.of A (ULift.{u + 1} A)) ≅ G.obj (ModuleCat.of A (ULift.{u + 1} A)))
    (he : ∀ f : ModuleCat.of A (ULift.{u + 1} A) ⟶ ModuleCat.of A (ULift.{u + 1} A),
      F.map f ≫ e.hom = e.hom ≫ G.map f)
    (P : CochainComplex (ModuleCat.{u + 1} A) ℤ) (n : ℤ → ℕ)
    (hP : P.X = fun q ↦ FiniteConstantModel.freeScalars A (n q)) :
    Nonempty ((F.mapHomologicalComplex (.up ℤ)).obj P ≅
      (G.mapHomologicalComplex (.up ℤ)).obj P) := by
  obtain ⟨X, d, s, dd⟩ := P
  subst hP
  exact ⟨HomologicalComplex.Hom.isoOfComponents
    (fun q ↦ scalarFreeComparison F G e (n q))
    (fun i j _ ↦ (scalarFreeComparison_natural F G e he (n i) (n j) (d i j)).symm)⟩

/-- The continuous scalar realization is additive, being right exact.
(auxiliary; not a blueprint node). -/
instance continuousScalarFunctor_additive (A : Type u) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] : (continuousScalarFunctor A).Additive :=
  rightExactFunctor_le_additiveFunctor _ _ _ (ContinuousScalarPresentation.continuous_colimits A)

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E]

/-- The inverse image of the completed constant model of a complex of finite free scalar
modules is the image, under the comparison equivalence `Φ`, of the pullback from the point of
the corresponding complex of free condensed modules.
(auxiliary; not a blueprint node). -/
theorem nonempty_adicTowerPullback_sfbCompletedModel_iso {X Y : Scheme.{u}} (h : Y ⟶ X)
    (Φ : AdicCompletion.Modules l E Y ⥤ Scheme.proEtaleRingModules Y
      ((Scheme.adicTowerInverseImage h).obj
        (Scheme.adicLisseCompletedRing X (Scheme.pbcIntegralDatum l E).ideal)))
    [Φ.IsEquivalence] [Φ.Additive]
    (α : integralRealization l E X ⋙
        Scheme.proEtaleRingModulePullback h
          (Scheme.adicLisseCompletedRing X (Scheme.pbcIntegralDatum l E).ideal) _
          (Iso.refl _) ≅
      CondensedRing.upperStar (DerivedNakayama.integerRing l E) h ⋙ Φ)
    (P : CochainComplex (ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E)) ℤ)
    (n : ℤ → ℕ)
    (hP : P.X = fun q ↦
      FiniteConstantModel.freeScalars (Padic.coefficientExtensionIntegers l E) (n q)) :
    Nonempty ((Scheme.adicTowerPullback h
        (Scheme.adicLisseCompletedRing X (Scheme.pbcIntegralDatum l E).ideal)).obj
        (Scheme.sfbCompletedModel X (Scheme.pbcIntegralDatum l E).ideal
          (((ModuleCat.restrictScalars.{u + 1}
            (ULift.ringEquiv : Scheme.PbcIntegralRing l E ≃+*
              Padic.coefficientExtensionIntegers l E).toRingHom).mapHomologicalComplex
                (.up ℤ)).obj P)) ≅
      Φ.mapDerivedCategory.obj (DerivedCategory.Q.obj
        (((CondensedRing.upperStarFromPointMod (DerivedNakayama.integerRing l E) Y
          ).mapHomologicalComplex (.up ℤ)).obj
          (((letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
            continuousScalarFunctor (Padic.coefficientExtensionIntegers l E)
            ).mapHomologicalComplex (.up ℤ)).obj P)))) := by
  let O := Padic.coefficientExtensionIntegers l E
  let d := Scheme.pbcIntegralDatum l E
  let Rs := Scheme.adicLisseCompletedRing X d.ideal
  let F₃ := Scheme.proEtaleRingModulePullback h Rs _ (Iso.refl _)
  let G := Scheme.pbcRestrict (Scheme.pbcCompletedComparison X d).hom ⋙ F₃
  let rs := ModuleCat.restrictScalars.{u + 1}
    (ULift.ringEquiv : Scheme.PbcIntegralRing l E ≃+* O).toRingHom
  let cs := letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
    continuousScalarFunctor O
  let cM := Scheme.adicLisseConstantModules X (Scheme.PbcIntegralRing l E)
  let cA := Scheme.completedAdicChange X (Scheme.CompletedConstantReduction.base X d.ideal)
  let upX := CondensedRing.upperStarFromPointMod (DerivedNakayama.integerRing l E) X
  let upY := CondensedRing.upperStarFromPointMod (DerivedNakayama.integerRing l E) Y
  let S := IntegralSectionScalars.sectionRealization l E X
  let T := IntegralSectionScalars.completedRealization l E X
  obtain ⟨hS, hT⟩ := IntegralSectionScalars.finiteColimits l E X
  have : S.Additive := rightExactFunctor_le_additiveFunctor _ _ _ hS
  have : T.Additive := rightExactFunctor_le_additiveFunctor _ _ _ hT
  have : cM.Additive := Scheme.CompletedConstantReduction.constant_additive X _
  have : cs.Additive := by
    let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
    exact rightExactFunctor_le_additiveFunctor _ _ _
      (ContinuousScalarPresentation.continuous_colimits O)
  obtain ⟨e, he⟩ := IntegralSectionScalars.regularComparison l E X
  obtain ⟨c⟩ := nonempty_mapHomologicalComplex_iso_of_freeScalars S T e he P n hP
  have hs : S ⋙ G = cs ⋙ upX ⋙ (integralRealization l E X ⋙ F₃) := by
    unfold S IntegralSectionScalars.sectionRealization
    rfl
  have ht : T ⋙ G = rs ⋙ (Scheme.integralConstantModule X d ⋙
      Scheme.pbcRestrict (Scheme.pbcCompletedComparison X d).hom) ⋙ F₃ := by
    unfold T IntegralSectionScalars.completedRealization
    rfl
  let i₁ : S ⋙ G ≅ cs ⋙ upY ⋙ Φ := eqToIso hs ≪≫
    Functor.isoWhiskerLeft cs (Functor.isoWhiskerLeft upX α ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        (CondensedRing.upperStarFromPointModComp (DerivedNakayama.integerRing l E) h) Φ)
  let i₂ : T ⋙ G ≅ rs ⋙ cM ⋙ cA ⋙ F₃ := eqToIso ht ≪≫
    Functor.isoWhiskerLeft rs (Functor.isoWhiskerRight
      (Scheme.completedModelRoundTrip X d) F₃)
  let P₀ := (rs.mapHomologicalComplex (.up ℤ)).obj P
  let j₁ : (F₃.mapHomologicalComplex (.up ℤ)).obj ((cA.mapHomologicalComplex (.up ℤ)).obj
      ((cM.mapHomologicalComplex (.up ℤ)).obj P₀)) ≅
      ((rs ⋙ cM ⋙ cA ⋙ F₃).mapHomologicalComplex (.up ℤ)).obj P :=
    HomologicalComplex.Hom.isoOfComponents (fun _ ↦ Iso.refl _) (by simp [P₀])
  let j₂ : ((T ⋙ G).mapHomologicalComplex (.up ℤ)).obj P ≅
      (G.mapHomologicalComplex (.up ℤ)).obj ((T.mapHomologicalComplex (.up ℤ)).obj P) :=
    HomologicalComplex.Hom.isoOfComponents (fun _ ↦ Iso.refl _) (by simp)
  let j₃ : (G.mapHomologicalComplex (.up ℤ)).obj ((S.mapHomologicalComplex (.up ℤ)).obj P) ≅
      ((S ⋙ G).mapHomologicalComplex (.up ℤ)).obj P :=
    HomologicalComplex.Hom.isoOfComponents (fun _ ↦ Iso.refl _) (by simp)
  let j₄ : ((cs ⋙ upY ⋙ Φ).mapHomologicalComplex (.up ℤ)).obj P ≅
      (Φ.mapHomologicalComplex (.up ℤ)).obj ((upY.mapHomologicalComplex (.up ℤ)).obj
        ((cs.mapHomologicalComplex (.up ℤ)).obj P)) :=
    HomologicalComplex.Hom.isoOfComponents (fun _ ↦ Iso.refl _) (by simp)
  exact ⟨F₃.mapDerivedCategoryFactors.app _ ≪≫
    DerivedCategory.Q.mapIso (j₁ ≪≫
      ((NatIso.mapHomologicalComplex i₂ (.up ℤ)).app P).symm ≪≫ j₂ ≪≫
      (G.mapHomologicalComplex (.up ℤ)).mapIso c.symm ≪≫ j₃ ≪≫
      (NatIso.mapHomologicalComplex i₁ (.up ℤ)).app P ≪≫ j₄) ≪≫
    (Φ.mapDerivedCategoryFactors.app _).symm⟩

/-- The continuous scalar realization of a finite free scalar module is free.
(auxiliary; not a blueprint node). -/
theorem isFree_continuousScalarFunctor_freeScalars (A : Type u) [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] (n : ℕ) :
    Mod.IsFree (Profinite.continuousCoefficientRingObj A)
      ((continuousScalarFunctor A).obj (FiniteConstantModel.freeScalars A n)) :=
  ⟨n, ⟨ContinuousScalarPresentation.continuousFreeIso A n⟩⟩

/-- A bounded-or-not complex of finite projective modules over the lifted ring `ULift O`, with
`O` local, is, after restriction of scalars along `ULift O ≃ O`, isomorphic to a complex whose
terms are the standard finite free `O`-modules.
(auxiliary; not a blueprint node). -/
theorem exists_freeScalars_complex {O : Type u} [CommRing O]
    [IsLocalRing (ULift.{u + 1} O)]
    (P : CochainComplex (ModuleCat.{u + 1} (ULift.{u + 1} O)) ℤ)
    (hP : ∀ q, Module.Projective (ULift.{u + 1} O) (P.X q) ∧
      Module.Finite (ULift.{u + 1} O) (P.X q)) :
    ∃ (P₀ : CochainComplex (ModuleCat.{u + 1} O) ℤ) (n : ℤ → ℕ),
      P₀.X = (fun q ↦ FiniteConstantModel.freeScalars O (n q)) ∧
        Nonempty (((ModuleCat.restrictScalars.{u + 1}
          (ULift.ringEquiv : ULift.{u + 1} O ≃+* O).toRingHom).mapHomologicalComplex
            (.up ℤ)).obj P₀ ≅ P) := by
  classical
  let A := ULift.{u + 1} O
  let F := ModuleCat.restrictScalars.{u + 1} (ULift.ringEquiv : A ≃+* O).toRingHom
  let hF : F.FullyFaithful :=
    (ModuleCat.restrictScalarsEquivalenceOfRingEquiv
      (ULift.ringEquiv : A ≃+* O)).fullyFaithfulFunctor
  have hfree (q : ℤ) : Module.Free A (P.X q) := by
    obtain ⟨_, _⟩ := hP q
    exact Module.free_of_flat_of_isLocalRing
  let n (q : ℤ) : ℕ := Module.finrank A (P.X q)
  let e (q : ℤ) : F.obj (FiniteConstantModel.freeScalars O (n q)) ≅ P.X q := by
    obtain ⟨_, _⟩ := hP q
    let b := Module.finBasis A (P.X q)
    let i : (Fin (n q) → A) ≃ₗ[A] F.obj (FiniteConstantModel.freeScalars O (n q)) :=
      { toFun := fun x ↦ x
        invFun := fun x ↦ x
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun _ _ ↦ rfl
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl }
    exact (b.equivFun.trans i).toModuleIso.symm
  let P₀ : CochainComplex (ModuleCat.{u + 1} O) ℤ :=
    { X := fun q ↦ FiniteConstantModel.freeScalars O (n q)
      d := fun i j ↦ hF.preimage ((e i).hom ≫ P.d i j ≫ (e j).inv)
      shape := fun i j hij ↦ hF.map_injective (by simp [P.shape i j hij])
      d_comp_d' := fun i j k _ _ ↦ hF.map_injective (by simp) }
  exact ⟨P₀, n, rfl, ⟨HomologicalComplex.Hom.isoOfComponents e (fun i j _ ↦ by
    change (e i).hom ≫ P.d i j = F.map (hF.preimage _) ≫ (e j).hom
    simp)⟩⟩

end AlgebraicGeometry.ProEtale
