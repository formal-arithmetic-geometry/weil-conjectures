/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C4
-/
module

public import Sheaf.Paper.FiniteProjectiveTensorProducts
public import Sheaf.Paper.CompletedConstantSheafReduction
import Sheaf.Algebra.Homology.ChangeOfRingsTensorCancellation
import all Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle

/-! # Derived scalar reduction from a strict-perfect residue resolution

Source: Stacks Tags 06YY and 06YU; blueprint finite-reduction-reconstruction, step 1.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
variable (T : Scheme.{t}) {A : Type (t + 1)} [CommRing A]
variable (d : ProEtaleAdicCoefficientDatum A)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem ordinaryReductionTensor (n : ℕ) :
    Nonempty (
    completedConstantExtension T (adicDatumProjection T d n) ⋙
        SheafOfModules.restrictScalars.{t + 1} ((adicLisseForget T).map
          (adicDatumProjection T d n)) ≅
      letI := SheafOfModules.monoidalCategory (adicDatumRing T d)
      MonoidalCategory.tensorLeft (CompletedConstantReduction.residue T d.ideal n)) := by
  let φ := adicDatumProjection T d n
  let U := SheafOfModules.restrictScalars.{t + 1} ((adicLisseForget T).map φ)
  let E := reductionChange T φ
  let := HasDerivedCategory.standard (adicDatumModules T d)
  let := HasDerivedCategory.standard (completedConstantModules T
    ((adicLisseRingSystem T d.ideal).obj (Opposite.op n)))
  let hE :=
    (SheafOfModules.derivedChangeOfRingsIndependentCoefficients.{t + 2, t + 1, t + 1, t}
      φ).choose_spec.choose
  have hEm {N N' : adicDatumModules T d} (a : N ⟶ N') :
      E.map a = eqToHom (hE N) ≫ SheafOfModules.changeOfRingsHom.{t, t + 1, t + 1} φ N a ≫
        eqToHom (hE N').symm :=
    (SheafOfModules.derivedChangeOfRingsIndependentCoefficients.{t + 2, t + 1, t + 1, t}
      φ).choose_spec
      |>.choose_spec.choose a
  let := SheafOfModules.monoidalCategory (adicDatumRing T d)
  let := SheafOfModules.monoidalCategory ((adicLisseRingSystem T d.ideal).obj (Opposite.op n))
  obtain ⟨c, hc⟩ := SheafOfModules.exists_changeOfRings_tensorCancellation φ
  let S := SheafOfModules.unit ((adicLisseForget T).obj
    ((adicLisseRingSystem T d.ideal).obj (Opposite.op n)))
  let e (N : adicDatumModules T d) : U.obj (E.obj N) ≅
      MonoidalCategoryStruct.tensorObj (U.obj S) N :=
    U.mapIso (eqToIso (hE N)) ≪≫
      U.mapIso (MonoidalCategory.leftUnitor
        (SheafOfModules.changeOfRings.{t, t + 1, t + 1} φ N)).symm ≪≫ c S N
  refine ⟨NatIso.ofComponents e ?_⟩
  intro N N' a
  change U.map (E.map a) ≫ (e N').hom =
    (e N).hom ≫ MonoidalCategoryStruct.whiskerLeft (U.obj S) a
  dsimp only [e, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, eqToIso.hom]
  rw [hEm]
  simp only [Functor.map_comp, Category.assoc]
  rw [← U.map_comp_assoc (eqToHom (hE N').symm) (eqToHom (hE N'))]
  simp only [eqToHom_trans, eqToHom_refl, U.map_id, Category.id_comp]
  congr 1
  rw [← U.map_comp_assoc, MonoidalCategory.leftUnitor_inv_naturality, U.map_comp,
    Category.assoc]
  congr 1
  have h := hc (𝟙 S) a
  change U.map (MonoidalCategoryStruct.tensorHom (𝟙 S)
    (SheafOfModules.changeOfRingsHom.{t, t + 1, t + 1} φ N a)) ≫ (c S N').hom =
      (c S N).hom ≫ MonoidalCategoryStruct.tensorHom (U.map (𝟙 S)) a at h
  simp only [MonoidalCategory.tensorHom_def, U.map_id] at h
  erw [MonoidalCategory.id_whiskerRight, Category.id_comp] at h
  have hi : MonoidalCategoryStruct.whiskerRight (𝟙 (U.obj S)) N = 𝟙 _ :=
    MonoidalCategory.id_whiskerRight _ _
  rw [hi, Category.id_comp] at h
  exact h

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- A bounded finite-free retract resolution of the restricted quotient computes the
underlying derived scalar-reduction functor.

Source: Stacks Tags 06YY and 06YU, tensor computation of derived scalar extension;
blueprint finite-reduction-reconstruction, step 1
(blueprint: lem-weil-pbc-completed-finite-reduction-tensor-comparison).
Proof: P is K-flat because it is bounded above and its terms split off finite powers
of the unit. On a K-flat complex C, tensor the augmentation with C. Its cone is acyclic
by K-flatness, so this gives a quasi-isomorphism from C tensor P to C tensor the
restricted quotient. The usual tensor-extension identification identifies the latter
with extension of C to the quotient followed by restriction. Both identifications
are natural in C. The universal scalar-extension comparison computes extension
on K-flat inputs. Cancel the invertible factors of adicDatumComplexCounit to obtain
invertibility of its homotopy counit. Descend through the K-flat localization, using its
full faithfulness on natural transformations and the quasi-isomorphism just proved.
The localization comparison defining finiteProjectiveTensorRight identifies its
restriction with C tensor P. Invert this descended comparison to obtain the stated
orientation. No flatness assumption on the quotient is used. -/
theorem completedFiniteReductionTensorComparison (n : ℕ)
    (P : CochainComplex (adicDatumModules T d) ℤ)
    (hb : ∃ a b : ℤ, ∀ j : ℤ, j < a ∨ b < j → IsZero (P.X j))
    (p : SheafOfModules.StrictPerfectCoefficientPackageOnSite
      ((adicLisseForget T).obj (adicDatumRing T d)) P)
    (α : P ⟶ (CochainComplex.singleFunctor _ 0).obj
      (CompletedConstantReduction.residue T d.ideal n))
    (hα : QuasiIso α) :
    Nonempty (adicDatumReductionUnderlying T d n ≅
      finiteProjectiveTensorRight T d P hb p) := by
  classical
  let R := adicDatumRing T d
  let S := (adicLisseRingSystem T d.ideal).obj (Opposite.op n)
  let φ := adicDatumProjection T d n
  let B := adicDatumModules T d
  let B' := completedConstantModules T S
  let := HasDerivedCategory.standard B
  let := HasDerivedCategory.standard B'
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.symmetricCategory R
  let := SheafOfModules.tensorPreadditive.{t + 1, t, t + 1} R
  let E := reductionChange T φ
  let U := SheafOfModules.restrictScalars.{t + 1} ((adicLisseForget T).map φ)
  let := (adicDatumRestriction_exact T φ).1
  let := (adicDatumRestriction_exact T φ).2
  let Q := completedConstantQ B
  let π := HomotopyCategory.quotient B (.up ℤ)
  let EH := E.mapHomotopyCategory (.up ℤ)
  let EC := E.mapHomologicalComplex (.up ℤ)
  let UC := U.mapHomologicalComplex (.up ℤ)
  let L := adicDatumExtension T φ
  let V := adicDatumRestriction T φ
  let F := finiteProjectiveTensorRight T d P hb p
  let ε := adicDatumExtensionCounit T φ
  let εV : DerivedCategory.Qh ⋙ (L ⋙ V) ⟶ (EH ⋙ DerivedCategory.Qh) ⋙ V :=
    (Functor.associator _ _ _).inv ≫ Functor.whiskerRight ε V
  obtain ⟨o⟩ := ordinaryReductionTensor T d n
  let o' := o ≪≫ BraidedCategory.tensorLeftIsoTensorRight (C := B)
    (CompletedConstantReduction.residue T d.ideal n)
  let τ := completedConstantTensor T R
  let b : finiteProjectiveTensorComplexRight T d P ⟶ (EC ⋙ UC) ⋙ Q :=
    Functor.whiskerRight (τ.flip.map α ≫
      (CochainComplex.map₂HomologicalComplexFlipObjSingleIso
        (MonoidalCategory.curriedTensor B)
        (CompletedConstantReduction.residue T d.ideal n)).hom ≫
      (Functor.mapHomologicalComplexCompIso o' (.up ℤ)).inv) Q
  let j : π ⋙ ((EH ⋙ DerivedCategory.Qh) ⋙ V) ≅ (EC ⋙ UC) ⋙ Q :=
    Functor.isoWhiskerRight (E.mapHomotopyCategoryFactors (.up ℤ))
      (DerivedCategory.Qh ⋙ V) ≪≫
      Functor.isoWhiskerLeft EC (Functor.isoWhiskerRight
        (DerivedCategory.quotientCompQhIso B') V) ≪≫
      Functor.isoWhiskerLeft EC U.mapDerivedCategoryFactors
  let β₀ : π ⋙ (DerivedCategory.Qh ⋙ F) ⟶
      π ⋙ ((EH ⋙ DerivedCategory.Qh) ⋙ V) :=
    (Functor.isoWhiskerRight (DerivedCategory.quotientCompQhIso B) F).hom ≫
      (finiteProjectiveTensorRightComparison T d P hb p).hom ≫ b ≫ j.inv
  let ff := Functor.FullyFaithful.ofFullyFaithful
    ((Functor.whiskeringLeft _ _ (adicDatumDerived T d)).obj π)
  let β : DerivedCategory.Qh ⋙ F ⟶ (EH ⋙ DerivedCategory.Qh) ⋙ V := ff.preimage β₀
  have hβ (C : CochainComplex B ℤ)
      (hC : CochainComplex.IsKFlatIndependentCoefficients (R := R) C) :
      IsIso (β.app (π.obj C)) := by
    have ht : QuasiIso ((τ.obj C).map α) :=
      SheafOfModules.tensor_left_quasiIso α hα hC
    have : IsIso (Q.map ((τ.flip.map α).app C)) :=
      (DerivedCategory.isIso_Q_map_iff_quasiIso B _).2 ht
    have hb : IsIso (b.app C) := by
      dsimp only [b, Functor.whiskerRight_app, NatTrans.comp_app]
      rw [Q.map_comp, Q.map_comp]
      infer_instance
    have hb₀ : IsIso (β₀.app C) := by
      dsimp only [β₀, NatTrans.comp_app]
      infer_instance
    have heq : β.app (π.obj C) = β₀.app C :=
      congrArg (fun a ↦ a.app C) (ff.map_preimage β₀)
    rw [heq]
    exact hb₀
  have hε (C : CochainComplex B ℤ)
      (hC : CochainComplex.IsKFlatIndependentCoefficients (R := R) C) :
      IsIso (ε.app (π.obj C)) := by
    let a := L.map ((DerivedCategory.quotientCompQhIso B).inv.app C)
    let c := (adicDatumQh T S).map ((E.mapHomotopyCategoryFactors (.up ℤ)).hom.app C)
    let e := (DerivedCategory.quotientCompQhIso B').hom.app (EC.obj C)
    have : IsIso a := inferInstance
    have : IsIso c := inferInstance
    have : IsIso e := inferInstance
    have : IsIso (a ≫ ε.app (π.obj C) ≫ c ≫ e) :=
      adicDatumComplexCounit_isIso T φ C hC
    have : IsIso (ε.app (π.obj C) ≫ c ≫ e) := IsIso.of_isIso_comp_left a _
    exact IsIso.of_isIso_comp_right _ (c ≫ e)
  let ℘ : ObjectProperty (HomotopyCategory B (.up ℤ)) :=
    fun X ↦ CochainComplex.IsKFlatIndependentCoefficients (R := R) X.as
  let W := HomotopyCategory.quasiIso B (.up ℤ)
  let ℓ := ℘.ι ⋙ (DerivedCategory.Qh (C := B))
  have hℓ : ℓ.IsLocalization (W.inverseImage ℘.ι) := by
    apply SheafOfModules.restriction_localization W DerivedCategory.Qh ℘
    intro X
    obtain ⟨C, f, hC, _, hf, _⟩ :=
      CochainComplex.exists_isKFlatResolutionIndependentCoefficients (R := R) X.as
    refine ⟨⟨π.obj C, hC⟩, π.map f, ?_⟩
    exact (HomotopyCategory.quotient_map_mem_quasiIso_iff f).2 hf
  let βP := Functor.whiskerLeft ℘.ι β
  let εP := Functor.whiskerLeft ℘.ι εV
  have : IsIso βP := (NatTrans.isIso_iff_isIso_app βP).mpr (fun X ↦ hβ X.obj.as X.property)
  have : IsIso εP := by
    apply (NatTrans.isIso_iff_isIso_app εP).mpr
    intro X
    have : IsIso (ε.app (℘.ι.obj X)) := hε X.obj.as X.property
    dsimp only [εP, Functor.whiskerLeft_app, εV, NatTrans.comp_app,
      Functor.associator_inv_app, Functor.whiskerRight_app]
    rw [Category.id_comp]
    exact Functor.map_isIso V (ε.app (℘.ι.obj X))
  let i : ℓ ⋙ F ≅ ℓ ⋙ (L ⋙ V) :=
    Functor.associator ℘.ι DerivedCategory.Qh F ≪≫
      asIso βP ≪≫ (asIso εP).symm ≪≫
      (Functor.associator ℘.ι DerivedCategory.Qh (L ⋙ V)).symm
  let full := Localization.fullyFaithfulWhiskeringLeft ℓ (W.inverseImage ℘.ι)
    (adicDatumDerived T d)
  exact ⟨(full.preimageIso i).symm⟩

end AlgebraicGeometry.Scheme
