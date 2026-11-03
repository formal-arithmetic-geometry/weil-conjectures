/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.StratifiedScalarPerfectGeneration
public import WeilConjectures.AlgebraicGeometry.FiniteCondensedCtfEquivalence
import all WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteScalarConstantModels
import all WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.PadicConstantLocalModelTor
import Mathlib.RingTheory.Finiteness.Projective
import WeilConjectures.AlgebraicGeometry.EtaleStratifiedPerfectCalculus
import all WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteEncodingPullbackFixed
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedPointModuleComparison
import WeilConjectures.SixFunctors.ProEtale.Comparison.UpperStar
import WeilConjectures.SixFunctors.ProEtale.Comparison.ConstantSheaf

/-! # Finite-coefficient scalar-perfect stratifications -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.FiniteDiscreteOrdinary

variable (A : Type u) [CommRing A] [Finite A]
  [TopologicalSpace A] [DiscreteTopology A] [IsTopologicalRing A]

attribute [local instance] canonicalAbelianMap_isMonHom

private def scalarExtensionConstantNatIso (T : Scheme.{u}) :
    finiteConstantScalarExtension (coefficient A) T ⋙
        Mod.comap (canonicalAbelianMap A T) ≅
      Mod.comap (scalarHom A) ⋙
        (constantSheaf (Scheme.ProEt.topology T) Ab.{u + 1}).mapMod
          (AddCommGrpCat.of (ULift.{u + 1} A)) := by
  let F := scalarConstant T
  let G := constantSheaf (Scheme.ProEt.topology T) Ab.{u + 1}
  let h := scalarHom A
  let φ := scalarCoefficientHom (coefficient A) T
  let κ := canonicalAbelianMap A T
  let α : G ≅ F := constantSchemeIso T
  letI : IsMonHom κ := canonicalAbelianMap_isMonHom A T
  letI : IsMonHom φ := scalarCoefficientHom_isMonHom (coefficient A) T
  letI : IsMonHom (inv φ) := IsMonHom.inv φ
  letI : IsMonHom (F.map h) := scalar_map_scalarHom A T
  letI : IsMonHom (α.hom.app (AddCommGrpCat.of (ULift.{u + 1} A))) := by
    have hi := Functor.isMonHom_compAlgHom
      (constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
      (upperStarFromPoint T) (constantSchemeIso T).inv
      (AddCommGrpCat.of (ULift.{u + 1} A))
    have hm : F.monObjObj (AddCommGrpCat.of (ULift.{u + 1} A)) =
        (upperStarFromPoint T).monObjObj
          ((constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).obj
            (AddCommGrpCat.of (ULift.{u + 1} A))) :=
      Functor.monObjObj_comp _ _ _
    have hi' := IsMonHom.of_eq _ hm.symm rfl (hf := hi)
    exact monHomInvExplicit (F.monObjObj _) (G.monObjObj _) (α.app _).symm hi'
  letI : IsMonHom (κ ≫ inv φ) := by infer_instance
  letI : IsMonHom (α.hom.app (AddCommGrpCat.of (ULift.{u + 1} A)) ≫ F.map h) :=
    by infer_instance
  have hs : α.hom.app (AddCommGrpCat.of (ULift.{u + 1} A)) ≫ F.map h = κ ≫ inv φ := by
    apply (cancel_mono φ).mp
    rw [Category.assoc, scalarCoefficient_normalization A T]
    simp [κ, φ, α]
  change (F.mapMod _ ⋙ Mod.extendScalars φ) ⋙ Mod.comap κ ≅ _
  exact Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (F.mapMod _)
      (Functor.isoWhiskerRight (Mod.extendScalarsIsoComapInv φ) (Mod.comap κ) ≪≫
        (Mod.comapComp κ (inv φ)).symm ≪≫ Mod.comapCongr hs.symm ≪≫
        Mod.comapComp (α.hom.app _) (F.map h)) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (F.mapModComapIso h).symm (Mod.comap (α.hom.app _)) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (Mod.comap h) (Functor.mapModNatIso α _).symm

private def constantModuleFunctor (T : Scheme.{u}) :
    Mod Ab.{u + 1} (AddCommGrpCat.of (ULift.{u + 1} A)) ⥤
      Mod (T.ProEtᵒᵖ ⥤ Ab.{u + 1})
        (ConstantInternalModuleSheafEncoding.A (C := T.ProEtᵒᵖ) (ULift.{u + 1} A)) where
  obj := constantPresheafModule A T
  map f := Mod.homMk ((Functor.const T.ProEtᵒᵖ).map f.hom) (by
    apply NatTrans.ext
    funext U
    exact IsModHom.smul_hom (A := AddCommGrpCat.of (ULift.{u + 1} A)) (f := f.hom))
  map_id M := by ext U; rfl
  map_comp f g := by ext U; rfl

private def scalarConstantNatIso (T : Scheme.{u}) (e : Encoding A T) :
    finiteConstantScalarExtension (coefficient A) T ⋙
        (e.ordinary.functor ⋙ e.fixed.functor) ≅
      scalarEncoding A ⋙ constantSheaf (Scheme.ProEt.topology T)
        (ModuleCat.{u + 1} (ULift.{u + 1} A)) := by
  let J := Scheme.ProEt.topology T
  let B := ULift.{u + 1} A
  let H := ConstantInternalModuleSheafEncoding.sheafEncoding J B (internalToModule B) rfl
  let C := (constantSheaf J Ab.{u + 1}).mapMod (AddCommGrpCat.of B)
  let P := (presheafToSheaf J Ab.{u + 1}).mapMod
    (ConstantInternalModuleSheafEncoding.A (C := T.ProEtᵒᵖ) B)
  let N := Mod.comap (D := Ab.{u + 1}) (scalarHom A)
  let G : (e.ordinary.functor ⋙ e.fixed.functor) ≅ constantInternalEncoding A T := by
    rw [e.ordinary_functor, e.fixed_functor]
    refine NatIso.ofComponents (encoding_constantInternal_iso A T e) ?_
    intro M N f
    ext U x
    rfl
  let I : C ⋙ constantBridge A T ≅ constantModuleFunctor A T ⋙ P :=
    NatIso.ofComponents (constantBridgeSheafifyIso A T) (by intro M N f; ext U x; rfl)
  let V : constantModuleFunctor A T ⋙
      ConstantInternalModuleSheafEncoding.modulePresheafEncoding B (internalToModule B) ≅
      internalToModule B ⋙ Functor.const T.ProEtᵒᵖ :=
    NatIso.ofComponents (fun _ ↦ NatIso.ofComponents (fun _ ↦ Iso.refl _)
      (fun _ ↦ by ext x; rfl)) (by intro M N f; ext U x; rfl)
  exact Functor.isoWhiskerLeft _ G ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (scalarExtensionConstantNatIso A T) (constantBridge A T ⋙ H) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft N ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight I H ≪≫ Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (constantModuleFunctor A T)
        (ConstantInternalModuleSheafEncoding.encSheafifyIso J B (internalToModule B) rfl) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight V (presheafToSheaf J (ModuleCat.{u + 1} B)) ≪≫
      Functor.associator _ _ _)

private abbrev pointScalars :
    Mod Ab.{u + 1} (scalarRingObj (coefficient A)) ⥤
      Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) (coefficient A) :=
  (constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).mapMod
    (scalarRingObj (coefficient A)) ⋙ Mod.extendScalars (scalarCounit (coefficient A))

private abbrev pointModelFunctor := (scalarEncoding A).inv ⋙ pointScalars A

private def pointScalarsFreeIso (n : ℕ) :
    (pointScalars A).obj (Mod.finiteFree (scalarRingObj (coefficient A)) n) ≅
      Mod.finiteFree (coefficient A) n :=
  (pointScalars A).mapBiproduct _ ≪≫ biproduct.mapIso (fun _ ↦
    (Mod.extendScalars (scalarCounit (coefficient A))).mapIso
      (Mod.isoMk (Iso.refl _) (by simp)) ≪≫
      Mod.regularExtensionIso (scalarCounit (coefficient A)))

private def pointModelFreeIso (n : ℕ) :
    (pointModelFunctor A).obj (ModuleCat.of (ULift.{u + 1} A)
      (Fin n → ULift.{u + 1} A)) ≅ Mod.finiteFree (coefficient A) n :=
  (pointScalars A).mapIso
    ((scalarEncoding A).inv.mapIso (scalarFreeCoordinates A n).toModuleIso.symm ≪≫
      (scalarEncoding A).asEquivalence.unitIso.symm.app _) ≪≫ pointScalarsFreeIso A n

omit [Finite A] [DiscreteTopology A] in
private theorem pointModel_projective (M : ModuleCat.{u + 1} (ULift.{u + 1} A))
    [Module.Projective (ULift.{u + 1} A) M] [Module.Finite (ULift.{u + 1} A) M] :
    FiniteProjectiveCondensedModule (Mon.mk (coefficient A)) ((pointModelFunctor A).obj M) := by
  obtain ⟨n, f, g, _, _, hfg⟩ :=
    Module.Finite.exists_comp_eq_id_of_projective (ULift.{u + 1} A) M
  let F := pointModelFunctor A
  let e := pointModelFreeIso A n
  refine ⟨n, F.map (ModuleCat.ofHom g) ≫ e.hom,
    e.inv ≫ F.map (ModuleCat.ofHom f), ?_⟩
  simp only [Category.assoc, Iso.hom_inv_id_assoc, ← F.map_comp]
  change F.map (ModuleCat.ofHom (f ∘ₗ g)) = _
  rw [hfg]
  exact F.map_id M

private def pointModelEncodedIso (T : Scheme.{u}) (e : Encoding A T) :
    (pointModelFunctor A ⋙ (upperStarFromPoint T).mapMod (coefficient A)) ⋙
        (e.ordinary.functor ⋙ e.fixed.functor) ≅
      constantSheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1} A)) :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (scalarEncoding A).inv
      ((Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (constantExtensionCompIso (coefficient A) T).symm _ ≪≫
        scalarConstantNatIso A T e) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (scalarEncoding A).asEquivalence.counitIso _ ≪≫
    Functor.leftUnitor _

private def encodingPullIso {T U : Scheme.{u}} (f : U ⟶ T)
    (eT : Encoding A T) (eU : Encoding A U) :
    CondensedRing.upperStar (coefficient A) f ⋙ (eU.ordinary.trans eU.fixed).functor ≅
      (eT.ordinary.trans eT.fixed).functor ⋙
        upperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) f := by
  let ET := eT.ordinary.trans eT.fixed
  let EU := eU.ordinary.trans eU.fixed
  let R := lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) f
  let i : CondensedRing.lowerStar (coefficient A) f ⋙ ET.functor ≅
      EU.functor ⋙ R := encodingPushforwardNatIso A T U f eT eU
  let k := Iso.isoCompInverse (H := ET) i ≪≫ Functor.associator _ _ _
  let kr := Iso.inverseCompIso (G := EU) k
  let a := ET.toAdjunction.comp
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} (ULift.{u + 1} A)) f)
  let b := (CondensedRing.upperStarLowerStarAdjunction (coefficient A) f).comp
    EU.toAdjunction
  exact (a.leftAdjointUniq (b.ofNatIsoRight kr)).symm

private def derivedEncodingPullIso {T U : Scheme.{u}} (f : U ⟶ T)
    (eT : Encoding A T) (eU : Encoding A U) :
    (CondensedRing.upperStar (coefficient A) f).mapDerivedCategory ⋙ eU.fixedDerived.functor ≅
      eT.fixedDerived.functor ⋙
        (upperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) f).mapDerivedCategory := by
  have : (eT.ordinary.trans eT.fixed).functor.Additive :=
    inferInstanceAs (eT.ordinary.functor ⋙ eT.fixed.functor).Additive
  have : (eU.ordinary.trans eU.fixed).functor.Additive :=
    inferInstanceAs (eU.ordinary.functor ⋙ eU.fixed.functor).Additive
  exact (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso (encodingPullIso A f eT eU) ≪≫
    Functor.mapDerivedCategoryCompIso _ _

private def derivedComparisonPullIso {T U : Scheme.{u}} (f : U ⟶ T) :
    (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) T).mapDerivedCategory ⋙
        (upperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) f).mapDerivedCategory ≅
      (Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) f).mapDerivedCategory ⋙
        (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) U).mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso
      (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} (ULift.{u + 1} A)) f) ≪≫
    Functor.mapDerivedCategoryCompIso _ _


private theorem locallyPerfect_of_encoded
    (enc : ∀ T : Scheme.{u}, Encoding A T) (S : Scheme.{u})
    (K : DerivedCategory (Internal A S))
    (L : Etale.DerivedCategoryModule (ULift.{u + 1} A) S)
    (e : (enc S).fixedDerived.functor.obj K ≅
      (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) S).mapDerivedCategory.obj L)
    (hL : Etale.IsLocallyConstantPerfectEtaleComplex (ULift.{u + 1} A) S L) :
    IsLocallyConstantPerfectComplex (coefficient A) S K := by
  obtain ⟨U, hU⟩ := hL
  refine ⟨U.weaken Scheme.etalePrecoverage_le_proetalePrecoverage, fun i ↦ ?_⟩
  obtain ⟨M, ⟨P, a, b, ha, hb, hP, ⟨eM⟩⟩, ⟨eL⟩⟩ := hU i
  let V := U.X i
  let f := U.f i
  let F := ((pointModelFunctor A).mapHomologicalComplex (.up ℤ)).obj P
  let G := CondensedRing.upperStarFromPointMod (coefficient A) V
  let H := ((enc V).ordinary.trans (enc V).fixed).functor
  have : H.Additive :=
    inferInstanceAs ((enc V).ordinary.functor ⋙ (enc V).fixed.functor).Additive
  have : ((upperStarFromPoint V).mapMod (coefficient A)).Additive :=
    inferInstanceAs G.Additive
  refine ⟨F, ⟨a, b, fun n hn ↦ ?_⟩, ?_, inferInstance, ⟨?_⟩⟩
  · apply (pointModelFunctor A).map_isZero
    rcases hn with hn | hn
    · exact (CochainComplex.isStrictlyGE_iff P a).mp ha n hn
    · exact (CochainComplex.isStrictlyLE_iff P b).mp hb n hn
  · intro n
    have := (hP n).1
    have := (hP n).2
    exact pointModel_projective A (P.X n)
  · let cE := constantSheaf V.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} A))
    let cP := constantSheaf (Scheme.ProEt.topology V)
      (ModuleCat.{u + 1} (ULift.{u + 1} A))
    let ν := comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) V
    let source : H.mapDerivedCategory.obj
        ((CondensedRing.upperStar (coefficient A) f).mapDerivedCategory.obj K) ≅
          DerivedCategory.Q.obj ((cP.mapHomologicalComplex (.up ℤ)).obj P) :=
      (derivedEncodingPullIso A f (enc S) (enc V)).app K ≪≫
      (upperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) f).mapDerivedCategory.mapIso e ≪≫
      (derivedComparisonPullIso A f).app L ≪≫
      ν.mapDerivedCategory.mapIso
        (eL ≪≫ cE.mapDerivedCategory.mapIso eM ≪≫ cE.mapDerivedCategoryFactors.app P) ≪≫
      ν.mapDerivedCategoryFactors.app _ ≪≫
      DerivedCategory.Q.mapIso ((Functor.mapHomologicalComplexCompIso
        (constantSheafCompComparisonUpperStarIso
          (ModuleCat.{u + 1} (ULift.{u + 1} A)) V) (.up ℤ)).app P)
    let target : H.mapDerivedCategory.obj
        (DerivedCategory.Q.obj ((G.mapHomologicalComplex (.up ℤ)).obj F)) ≅
          DerivedCategory.Q.obj ((cP.mapHomologicalComplex (.up ℤ)).obj P) :=
      H.mapDerivedCategoryFactors.app _ ≪≫
      DerivedCategory.Q.mapIso
        ((Functor.mapHomologicalComplexCompIso (pointModelEncodedIso A V (enc V))
          (.up ℤ)).app P)
    exact H.mapDerivedCategory.preimageIso (source ≪≫ target.symm)

/-- Finite condensed ctf complexes have a finite scalar-perfect stratification.
Source: blueprint internal-Hom stability proof, paragraph 1, finite coefficients;
ordinary etale finite stratified-perfect calculus
(blueprint: lem-sfb-finite-scalar-perfect-stratification).

Proof: descend the finite constructible finite-Tor complex through the finite-coefficient
etale realization equivalence. The ordinary finite stratified-perfect calculus supplies
one finite locally closed stratification and etale local bounded finite-projective scalar
models. Restriction commutes with the normalized encoding, by uniqueness of left adjoints.
The comparison inverse image preserves constant complexes. Extend each ordinary scalar
model to the condensed point: a finite projective module is a retract of a finite free
module, and scalar extension carries its two retract maps and their identity to a retract
of a finite free condensed module. Map the entire complex, including its differentials.
The natural constant-encoding comparison identifies its point pullback with the given
local model. Etale covers are pro-etale covers. Zero ranks and empty strata are retained. -/
theorem finite_scalarPerfectStratification
    (p ℓ : ℕ) [Fact p.Prime] [Fact ℓ.Prime] (hpℓ : p ≠ ℓ)
    (k : Type u) [Field k] [CharP k p]
    (T : Scheme.{u}) (a : T ⟶ Spec (.of k))
    [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a]
    (K : DerivedCategory (Internal A T))
    (hK : constantModelBoundedConstructible (coefficient A) T K ∧
      DerivedCategory.finiteTorAmplitude _ K) :
    CondensedRing.HasScalarPerfectStratification (coefficient A) T K := by
  classical
  let enc (T : Scheme.{u}) : Encoding A T := (encoding_exists A T).some
  obtain ⟨hF, hEquiv⟩ := finiteCondensedCtfEquivalence p ℓ hpℓ k A enc T a
  let P := Etale.DerivedCategory.isBoundedConstructible (ULift.{u + 1} A) T ⊓
    _root_.DerivedCategory.finiteTorAmplitude _
  let Q := constantModelBoundedConstructible (coefficient A) T ⊓
    _root_.DerivedCategory.finiteTorAmplitude _
  let R := ObjectProperty.lift Q (P.ι ⋙ internalEtaleRealization A T (enc T)) hF
  have : R.IsEquivalence := hEquiv
  let L := R.objPreimage ⟨K, hK⟩
  let eK : (internalEtaleRealization A T (enc T)).obj L.obj ≅ K :=
    Q.ι.mapIso (R.objObjPreimageIso ⟨K, hK⟩)
  have : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian a
  have : CompactSpace T := QuasiCompact.compactSpace_of_compactSpace a
  have ht : ∃ c d : ℤ,
      Etale.DerivedCategory.hasTorAmplitudeIn (ULift.{u + 1} A) T c d L.obj := by
    obtain ⟨c, d, ht⟩ := L.property.2
    exact ⟨c, d, Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.mpr ht⟩
  obtain ⟨s, hc, hs⟩ :=
    ((Etale.etaleStratifiedPerfect_calculus (ULift.{u + 1} A) T).1 L.obj).mpr
      ⟨L.property.1, ht⟩
  let s' : Scheme.Stratification T :=
    { s with isConstructible_stratum := hc }
  refine ⟨s', fun i ↦ ?_⟩
  apply locallyPerfect_of_encoded A enc (s.domain i) _ _ _ (hs i)
  exact (derivedEncodingPullIso A (s.immersion i) (enc T) (enc (s.domain i))).app K ≪≫
    (upperStar (ModuleCat.{u + 1} (ULift.{u + 1} A))
      (s.immersion i)).mapDerivedCategory.mapIso
        ((enc T).fixedDerived.functor.mapIso eK.symm ≪≫
          (enc T).fixedDerived.counitIso.app _) ≪≫
    (derivedComparisonPullIso A (s.immersion i)).app L.obj

end AlgebraicGeometry.ProEtale.FiniteDiscreteOrdinary
