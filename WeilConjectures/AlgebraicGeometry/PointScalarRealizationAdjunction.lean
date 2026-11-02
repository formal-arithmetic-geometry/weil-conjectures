/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.PointDualityCoefficientsFiber
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedScalarRealization
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Reflective
import WeilConjectures.CategoryTheory.ModuleObjects.MapModMonoidal
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedLisseEvaluationModel
import WeilConjectures.CategoryTheory.ZetaWeil.ContractibleDerivedSectionsTensor
import WeilConjectures.CategoryTheory.InternalSectionTensorComparison
import WeilConjectures.CategoryTheory.Monoidal.KFlatEquivalence
import Mathlib.CategoryTheory.Localization.Monoidal.Functor
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.CategoryTheory.RingedKFlatModel.RingedKFlatNativeModelIdentification
import WeilConjectures.Algebra.Homology.Ringed.RingedDerivedTensorNativeSupplement
import WeilConjectures.Algebra.Homology.Monoidal.MapHomologicalComplex
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Evaluation.ContractibleRealizationUnderivedModel
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Evaluation.ContractibleRealizationOrdinaryUnit
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MonoidalStructure
import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction

/-! # Scalar realization and singleton evaluation at a geometric point -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale

open CondensedRing.Evaluation

private theorem singleton_sections_colimits
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] : PreservesColimitsOfSize.{u + 1, u + 1}
    (CondensedRing.Evaluation.sections (coherentTopology Profinite.{u}) Λ
      (⊤_ Profinite.{u})) := by
  constructor
  intro I hI
  let J := coherentTopology Profinite.{u}
  let R := (sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
    (condensedSectionRing Λ)
  let M := SheafOfModules.evaluation.{u + 1} R (op (⊤_ Profinite.{u}))
  let E := (sheafSections J Ab.{u + 1}).obj (op (⊤_ Profinite.{u}))
  have : PreservesColimitsOfShape I E := singleton_abelian_colimits I
  have : PreservesColimitsOfShape I (SheafOfModules.toSheaf R) :=
    ((moduleSheaves_colimits_forgetful.{u + 1, u, u + 1, u + 1} R).2.2.2.2.2 I).2.1
  let U := forget₂ (ModuleCat.{u + 1} (R.obj.obj (op (⊤_ Profinite.{u})))) Ab.{u + 1}
  have : PreservesColimitsOfShape I (M ⋙ U) :=
    inferInstanceAs (PreservesColimitsOfShape I (SheafOfModules.toSheaf R ⋙ E))
  have : PreservesColimitsOfShape I M :=
    preservesColimitsOfShape_of_reflects_of_preserves M U
  exact inferInstanceAs (PreservesColimitsOfShape I
    ((InternalAbelianSheafModule.sectionModuleEquivalence J Λ).functor ⋙ M))

private theorem scalar_base_adjunction
    (O : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj O] [IsCommMonObj O] :
    letI : HasDerivedCategory.{u + 1} (ModuleCat.{u + 1} (condensedScalarRing O)) :=
      HasDerivedCategory.ofIsGrothendieckAbelian _
    Nonempty (CondensedRing.Evaluation.F (coherentTopology Profinite.{u}) O
      (⊤_ Profinite.{u}) terminalIsTerminal).Monoidal ∧
      ∃ adj : CondensedRing.Evaluation.F (coherentTopology Profinite.{u}) O
          (⊤_ Profinite.{u}) terminalIsTerminal ⊣
        CondensedRing.Evaluation.G (coherentTopology Profinite.{u}) O (⊤_ Profinite.{u}),
        IsIso adj.unit := by
  let J := coherentTopology Profinite.{u}
  let U := ⊤_ Profinite.{u}
  let : HasDerivedCategory.{u + 1} (ModuleCat.{u + 1} (condensedScalarRing O)) :=
    HasDerivedCategory.ofIsGrothendieckAbelian _
  obtain ⟨L, hadd, hflat, hpres, hbraid, ⟨adj₀⟩, ⟨eL⟩⟩ :=
    realization_underived_model J O U terminalIsTerminal
  let := hadd
  let := hflat
  let := hpres
  let : L.IsLeftAdjoint := ⟨_, ⟨adj₀⟩⟩
  let adj : F J O U terminalIsTerminal ⊣ G J O U := adj₀.derivedAdjunction.ofNatIsoLeft eL
  have hsym : strongSymmetric J O U terminalIsTerminal := by
    let := DerivedCategory.braidedCategory' (ModuleCat.{u + 1} (A J O U))
    let := DerivedCategory.braidedCategory' (Mod (Sheaf J Ab.{u + 1}) O)
    let := hbraid
    let b := L.leftDerivedFunctorBraided (fun X Y ↦ by
      simp only [Functor.map_braiding, Category.assoc, Functor.Monoidal.μ_δ,
        Category.comp_id])
    let := b
    let : L.leftDerivedFunctor.Monoidal := b.toMonoidal
    let := Functor.Monoidal.transport eL
    let : NatTrans.IsMonoidal eL.hom :=
      Functor.Monoidal.natTransIsMonoidal_of_transport eL
    exact ⟨{ braided := (Functor.LaxBraided.ofNatIso eL).braided }⟩
  let : PreservesFiniteLimits (sections J O U) := by infer_instance
  let : PreservesFiniteColimits (sections J O U) := by infer_instance
  have hcol := singleton_sections_colimits O
  have hu : IsIso adj₀.unit :=
    contractible_realization_ordinary_unit J O U terminalIsTerminal hcol L adj₀
  let := hu
  have hhu : IsIso (adj₀.mapHomotopyCategory (.up ℤ)).unit := by
    apply (adj₀.mapHomotopyCategory (.up ℤ)).isIso_unit_of_iso
    exact Functor.mapHomotopyCategoryCompIso (asIso adj₀.unit).symm (.up ℤ) ≪≫
      Functor.mapHomotopyCategoryIdIso _ _
  let := hhu
  have hdu : IsIso adj₀.derivedAdjunction.unit := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro X
    obtain ⟨P, hP, ⟨eP⟩⟩ := L.exists_kFlatKFlatMap_iso X
    rw [← NatTrans.isIso_app_iff_of_iso _ eP]
    have := L.isIso_leftDerivedFunctorCounit_app_of_kFlat' P hP.1
    have hfac := (adj₀.mapHomotopyCategory (.up ℤ)).derivedη_fac_app
      (HomotopyCategory.quasiIso _ (.up ℤ)) L.leftDerivedFunctorCounit
      (sections J O U).rightDerivedFunctorUnit P
    have hi : IsIso (adj₀.derivedAdjunction.unit.app (DerivedCategory.Qh.obj P) ≫
        (sections J O U).rightDerivedFunctor.map
          (L.leftDerivedFunctorCounit.app P)) := by
      change IsIso (((adj₀.mapHomotopyCategory (.up ℤ)).derivedη
        (HomotopyCategory.quasiIso _ (.up ℤ)) L.leftDerivedFunctorCounit
        (sections J O U).rightDerivedFunctorUnit).app _ ≫ _)
      rw [hfac]
      infer_instance
    exact IsIso.of_isIso_comp_right _
      ((sections J O U).rightDerivedFunctor.map (L.leftDerivedFunctorCounit.app P))
  let := hdu
  have hunit : IsIso adj.unit := by
    dsimp only [adj]
    rw [Adjunction.ofNatIsoLeft_unit]
    infer_instance
  obtain ⟨b⟩ := hsym
  exact ⟨⟨b.toMonoidal⟩, adj, hunit⟩

/-- The actual scalar realization is fully faithful and left adjoint to the fixed fiber;
the former is strong monoidal for the ordinary relative derived tensors.

Source: HRS Lemma 4.1(1), formulas (3.1)--(3.2), and Bhatt--Scholze Example 4.1.10.
(blueprint: lem-pod-point-scalar-realization-adjunction).

Proof: transport along the exact symmetric monoidal equivalence between the pro-etale
topos of an algebraically closed field and the condensed point. Every cover of the
singleton splits. Consequently singleton sections preserve finite limits and all
colimits, while scalar extension is strong symmetric monoidal. Constant scalar
extension is left adjoint to these sections; its unit is the identity on the regular
module, hence on free presentations. Derive this adjunction on flat-term K-flat
resolutions, using exact sections. Compare the fixed coefficient-extension model with
this derived left adjoint through its universal K-flat counit. Transport back to the
scheme point. The ring is exactly the reconstructed section ring at the singleton,
and the right functor is the inverse point equivalence followed by derived sections,
so these comparisons yield the displayed functors, not unspecified equivalences. -/
theorem point_scalar_realization_adjunction
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    (k : Type u) [Field k] [IsAlgClosed k] :
    Nonempty (condensedScalarRealization Λ.X (Spec (.of k))).Monoidal ∧
      ∃ adj : condensedScalarRealization Λ.X (Spec (.of k)) ⊣ pointDualityFiber Λ.X k,
        IsIso adj.unit := by
  classical
  let : HasDerivedCategory.{u + 1}
      (ModuleCat.{u + 1} (condensedScalarRing Λ.X)) :=
    HasDerivedCategory.ofIsGrothendieckAbelian _
  let : PreservesFiniteLimits (upperStarFromPoint (Spec (.of k))) := by
    unfold upperStarFromPoint pointUpperStar
    infer_instance
  let : PreservesFiniteColimits (upperStarFromPoint (Spec (.of k))) := by
    let : pointUpperStar.{u}.IsLeftAdjoint :=
      pointUpperStarLowerStarAdjunction.isLeftAdjoint
    unfold upperStarFromPoint
    infer_instance
  let : (upperStarFromPoint (Spec (.of k))).Braided := {}
  let : ((upperStarFromPoint (Spec (.of k))).mapMod Λ.X).Additive :=
    Functor.additive_of_preserves_binary_products _
  let : ((upperStarFromPoint (Spec (.of k))).mapMod Λ.X).Monoidal := inferInstance
  obtain ⟨me⟩ := exactEquivalenceMonoidal
    ((upperStarFromPoint (Spec (.of k))).mapMod Λ.X)
  let e := ((upperStarFromPoint (Spec (.of k))).mapMod Λ.X).asEquivalence
  let : e.functor.Additive := Functor.additive_of_preserves_binary_products e.functor
  let := Functor.additive_of_preserves_binary_products e.inverse
  obtain ⟨⟨m⟩, a, ha⟩ := scalar_base_adjunction Λ.X
  let := m
  let := ha
  let := me
  let d := e.mapDerivedCategory
  let : d.functor.Monoidal := me
  let a' := a.comp d.toAdjunction
  let ff := a.fullyFaithfulLOfIsIsoUnit
  let := ff.full
  let := ff.faithful
  have : IsIso a'.unit := a'.unit_isIso_of_L_fully_faithful
  let i : CondensedRing.Evaluation.F (coherentTopology Profinite.{u}) Λ.X
      (⊤_ Profinite.{u}) terminalIsTerminal ⋙ d.functor ≅
      condensedScalarRealization Λ.X (Spec (.of k)) := Iso.refl _
  let adj : condensedScalarRealization Λ.X (Spec (.of k)) ⊣ pointDualityFiber Λ.X k :=
    a'.ofNatIsoLeft i
  let : (CondensedRing.Evaluation.F (coherentTopology Profinite.{u}) Λ.X
      (⊤_ Profinite.{u}) terminalIsTerminal ⋙ d.functor).Monoidal := inferInstance
  refine ⟨⟨Functor.Monoidal.transport i⟩, adj, ?_⟩
  dsimp only [adj]
  rw [Adjunction.ofNatIsoLeft_unit]
  infer_instance

end AlgebraicGeometry.ProEtale
