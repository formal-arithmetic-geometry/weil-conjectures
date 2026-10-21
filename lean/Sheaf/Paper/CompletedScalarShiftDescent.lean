/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F3
-/
module

public import Sheaf.Paper.IntegralScalarExtensionUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
import Sheaf.Paper.IntegralReductionTowerUnrestricted
import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients

/-! # Normalized descent of the strict scalar shift

Source: Stacks Project, Tags 011G, 014E, 06YS, 06YT and 08TC.
(blueprint: lem-weil-completed-scalar-shift-descent)
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 1024
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite
namespace WeilConjectures
attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L) (Y : AlgebraicGeometry.Scheme.{t})


attribute [local instance] SheafOfModules.isMonoidal_W_independentCoefficients
  SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients
  SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients

private lemma acyclic_shift {A : Type*} [Category A] [Abelian A]
    (K : CochainComplex A ℤ) (hK : K.Acyclic) (m : ℤ) : (K⟦m⟧).Acyclic := by
  apply (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _).mp
  apply (HomotopyCategory.subcategoryAcyclic A).prop_of_iso
    ((HomotopyCategory.quotient A (.up ℤ)).commShiftIso m |>.app K).symm
  exact (HomotopyCategory.subcategoryAcyclic A).le_shift m _
    ((HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _).mpr hK)

private lemma acyclic_of_iso {A : Type*} [Category A] [Abelian A]
    {K K' : CochainComplex A ℤ} (e : K ≅ K') (hK : K.Acyclic) : K'.Acyclic := by
  intro i
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  exact Limits.IsZero.of_iso (hK i).isZero_homology
    ((HomologicalComplex.homologyFunctor A (.up ℤ) i).mapIso e).symm

private lemma good_shift (P : CochainComplex (integralTowerModules l E Y) ℤ)
    (hP : integralOperationsGoodComplex l E Y P) (m : ℤ) :
    integralOperationsGoodComplex l E Y (P⟦m⟧) := by
  let R := completedIntegralCommRingSheafUnrestricted l E Y
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients R
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients R
  have (M : SheafOfModules ((sheafCompose (AlgebraicGeometry.Scheme.ProEt.topology Y)
      (forget₂ CommRingCat RingCat)).obj R)) : (MonoidalCategory.tensorLeft M).Additive :=
    SheafOfModules.tensorLeft_additive_independent R M
  refine ⟨?_, ?_⟩
  · intro F hF
    exact acyclic_of_iso
      (CochainComplex.mapBifunctorShift₂Iso F P (MonoidalCategory.curriedTensor _) m).symm
      (acyclic_shift _ (hP.1 F hF) m)
  · intro i
    exact hP.2 (i + m)


private theorem good_whisker_full (Z : Type*) [Category Z] :
    ((Functor.whiskeringLeft _ _ Z).obj
      (integralOperationsGoodLocalization l E Y)).Full := by
  obtain ⟨P, hP, ⟨H, hH, ⟨eH⟩⟩, _⟩ :=
    SheafOfModules.site_derived_tensor_descent_independentCoefficients.{_, _, _, _, 0, 0}
      (AlgebraicGeometry.Scheme.ProEt.topology Y)
      (completedIntegralCommRingSheafUnrestricted l E Y)
  let A := SheafOfModules.{max u (t + 1)} ((sheafCompose (AlgebraicGeometry.Scheme.ProEt.topology Y)
    (forget₂ CommRingCat RingCat)).obj (completedIntegralCommRingSheafUnrestricted l E Y))
  let V := (HomotopyCategory.quasiIso A (.up ℤ)).inverseImage P.ι
  let Lg := P.ι ⋙ (DerivedCategory.Qh : HomotopyCategory A (.up ℤ) ⥤ _)
  have : H.IsEquivalence := hH
  have : V.Q.IsLocalization V := inferInstance
  have : Lg.IsLocalization V := by
    have : (V.Q ⋙ H).IsLocalization V := inferInstance
    exact Functor.IsLocalization.of_iso V eH
  refine ⟨?_⟩
  intro F G τ
  let τh : Lg ⋙ F ⟶ Lg ⋙ G :=
    { app := fun X ↦ τ.app ⟨X.obj.as, (hP X.obj).mp X.property⟩
      naturality := by
        intro X X' f
        have h := τ.naturality (ObjectProperty.homMk f.hom.out :
          (⟨X.obj.as, (hP X.obj).mp X.property⟩ :
            (integralOperationsGoodComplex l E Y).FullSubcategory) ⟶
          ⟨X'.obj.as, (hP X'.obj).mp X'.property⟩)
        have hq : DerivedCategory.Q.map f.hom.out = DerivedCategory.Qh.map f.hom := by
          have hh := DerivedCategory.quotientCompQhIso_hom_naturality f.hom.out
          simp only [DerivedCategory.quotientCompQhIso,
            HomologicalComplexUpToQuasiIso.quotientCompQhIso,
            CategoryTheory.Quotient.lift.isLift_hom,
            HomotopyCategory.quotient_map_out] at hh
          erw [Category.id_comp, Category.comp_id] at hh
          exact hh.symm
        change F.map (DerivedCategory.Q.map f.hom.out) ≫ _ =
          _ ≫ G.map (DerivedCategory.Q.map f.hom.out) at h
        change F.map (DerivedCategory.Qh.map f.hom) ≫ _ =
          _ ≫ G.map (DerivedCategory.Qh.map f.hom)
        simpa only [hq] using h }
  let ff := Localization.fullyFaithfulWhiskeringLeft Lg V Z
  refine ⟨ff.preimage τh, ?_⟩
  ext X
  have h := congrArg (fun a ↦ a.app ⟨
    (HomotopyCategory.quotient _ (.up ℤ)).obj X.obj,
    (hP _).mpr X.property⟩) (ff.map_preimage τh)
  exact h


private theorem goodLocalization_essSurj :
    (integralOperationsGoodLocalization l E Y).EssSurj := by
  obtain ⟨P, hP, ⟨H, hH, ⟨eH⟩⟩, _⟩ :=
    SheafOfModules.site_derived_tensor_descent_independentCoefficients.{_, _, _, _, 0, 0}
      (AlgebraicGeometry.Scheme.ProEt.topology Y)
      (completedIntegralCommRingSheafUnrestricted l E Y)
  let A := SheafOfModules.{max u (t + 1)}
    ((sheafCompose (AlgebraicGeometry.Scheme.ProEt.topology Y)
      (forget₂ CommRingCat RingCat)).obj (completedIntegralCommRingSheafUnrestricted l E Y))
  let V := (HomotopyCategory.quasiIso A (.up ℤ)).inverseImage P.ι
  let Lg := P.ι ⋙ (DerivedCategory.Qh : HomotopyCategory A (.up ℤ) ⥤ _)
  have : H.IsEquivalence := hH
  have : Lg.IsLocalization V := by
    have : (V.Q ⋙ H).IsLocalization V := inferInstance
    exact Functor.IsLocalization.of_iso V eH
  have : Lg.EssSurj := Localization.essSurj Lg V
  constructor
  intro K
  obtain ⟨X, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage Lg K
  exact ⟨⟨X.obj.as, (hP X.obj).mp X.property⟩, ⟨e⟩⟩

private theorem whiskeringLeft_faithful
    {C D B : Type*} [Category C] [Category D] [Category B]
    (Q : C ⥤ D) [Q.EssSurj] :
    ((Functor.whiskeringLeft C D B).obj Q).Faithful where
  map_injective := by
    intro F G α β h
    ext K
    obtain ⟨X, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage Q K
    apply (cancel_epi (F.map e.hom)).mp
    rw [α.naturality, β.naturality]
    exact congrArg (· ≫ G.map e.hom) (NatTrans.congr_app h X)


private theorem descentShift
    {C D B : Type*} [Category C] [Category D] [Category B]
    [HasShift C ℤ] [HasShift D ℤ] [HasShift B ℤ]
    (Q : C ⥤ D) [Q.CommShift ℤ] (H : C ⥤ B) [H.CommShift ℤ]
    (F : D ⥤ B) (e : Q ⋙ F ≅ H)
    (ff : ((Functor.whiskeringLeft C D B).obj Q).FullyFaithful) :
    ∃ s : F.CommShift ℤ, ∀ (a : ℤ) (X : C),
      (Functor.commShiftIso F (self := s) a).hom.app (Q.obj X) ≫
        (e.hom.app X)⟦a⟧' =
      F.map ((Q.commShiftIso a).inv.app X) ≫ e.hom.app (X⟦a⟧) ≫
        (H.commShiftIso a).hom.app X := by
  let j (a : ℤ) : Q ⋙ shiftFunctor D a ⋙ F ≅ Q ⋙ F ⋙ shiftFunctor B a :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (Q.commShiftIso a).symm F ≪≫
      Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ e ≪≫
      H.commShiftIso a ≪≫ Functor.isoWhiskerRight e.symm _ ≪≫ Functor.associator _ _ _
  let i (a : ℤ) : shiftFunctor D a ⋙ F ≅ F ⋙ shiftFunctor B a :=
    ff.preimageIso (j a)
  have hi (a : ℤ) (X : C) :
      (i a).hom.app (Q.obj X) =
        F.map ((Q.commShiftIso a).inv.app X) ≫ e.hom.app (X⟦a⟧) ≫
          (H.commShiftIso a).hom.app X ≫ (e.inv.app X)⟦a⟧' := by
    have h := NatTrans.congr_app (ff.map_preimage (j a).hom) X
    exact h.trans (by simp [j])
  let s : F.CommShift ℤ :=
    { commShiftIso := i
      commShiftIso_zero := by
        ext1
        apply ff.map_injective
        ext X
        dsimp
        simp only [hi, Functor.comp_obj, Functor.commShiftIso_zero,
          Functor.CommShift.isoZero_inv_app, Functor.map_comp,
          Functor.CommShift.isoZero_hom_app, Category.assoc,
          ← NatTrans.naturality_assoc, ← NatTrans.naturality]
        dsimp
        simp only [← Functor.map_comp_assoc, ← Functor.map_comp,
          Iso.inv_hom_id_app, Functor.id_obj, CategoryTheory.Functor.map_id, Category.id_comp,
          Iso.hom_inv_id_app_assoc]
      commShiftIso_add a b := by
        ext1
        apply ff.map_injective
        ext X
        dsimp
        simp only [hi, Functor.comp_obj, Functor.commShiftIso_add,
          Functor.CommShift.isoAdd_inv_app, Functor.map_comp,
          Functor.CommShift.isoAdd_hom_app, Category.assoc]
        congr 1
        rw [← cancel_epi (F.map ((shiftFunctor D b).map ((Q.commShiftIso a).hom.app X))),
          ← F.map_comp_assoc, ← Functor.map_comp, Iso.hom_inv_id_app,
          CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.id_comp]
        conv_lhs =>
          erw [← NatTrans.naturality_assoc]
          dsimp
          rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc, Category.assoc,
            ← Functor.map_comp, Iso.inv_hom_id_app]
          dsimp
          rw [CategoryTheory.Functor.map_id, Category.comp_id, ← NatTrans.naturality]
          dsimp
        conv_rhs =>
          erw [← NatTrans.naturality_assoc]
          dsimp
          rw [← Functor.map_comp_assoc, ← Functor.map_comp, Iso.hom_inv_id_app]
          dsimp
          rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.id_comp, hi,
            Category.assoc, Category.assoc, Category.assoc, ← Functor.map_comp_assoc,
            Iso.inv_hom_id_app, CategoryTheory.Functor.map_id, Category.id_comp] }
  refine ⟨s, ?_⟩
  intro a X
  change (i a).hom.app (Q.obj X) ≫ _ = _
  rw [hi]
  simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id]
  erw [Category.comp_id]


private theorem good_stable :
    (integralOperationsGoodComplex l E Y).IsStableUnderShift ℤ where
  isStableUnderShiftBy m := ⟨fun P hP ↦ good_shift l E Y P hP m⟩


/-- A coherent chain shift descends with the retained strict-scalar comparison.
Source: Stacks Project, Tags 06YS, 06YT and 08TC; step 6 of
lem-weil-point-completed-scalar-shift.
(blueprint: lem-weil-completed-scalar-shift-descent).
Proof: flat-term K-flat complexes are stable under integer shifts. Flat terms are
reindexed; the signed total-tensor reindexing preserves K-flatness. Localize their
homotopy category at quasi-isomorphisms, using the resolving-class equivalence with
the derived category. The given chain shift, followed by Q's shift comparison,
is natural and invertible on these representatives. It descends along the
equivalence to the strict scalar extension, transported through the retained
comparison integralScalarExtensionComparisonOfUniverses. This transport gives
exactly the displayed normalization equation. The zero and addition equations
hold on representatives by the coherent chain shift and Q's coherence, hence
globally by localization faithfulness. This proves a CommShift structure without
using the ordinary scalar extension or its completion comparison. -/
theorem completedScalarShiftDescent
    (eC : (integralScalarComplexFunctor l E L ι Y).CommShift ℤ) :
    ∃ eL : (integralScalarExtensionOfUniverses l E L ι Y).CommShift ℤ,
      ∀ (P : (integralOperationsGoodComplex l E Y).FullSubcategory) (m : ℤ),
    ∃ hP : integralOperationsGoodComplex l E Y (P.obj⟦m⟧),
      (Functor.commShiftIso (integralScalarExtensionOfUniverses l E L ι Y) (self := eL) m).hom.app
            (DerivedCategory.Q.obj P.obj) ≫
          ((integralScalarExtensionComparisonOfUniverses l E L ι Y).hom.app P)⟦m⟧' =
        (integralScalarExtensionOfUniverses l E L ι Y).map
            ((DerivedCategory.Q.commShiftIso m).inv.app P.obj) ≫
          (integralScalarExtensionComparisonOfUniverses l E L ι Y).hom.app
            ⟨P.obj⟦m⟧, hP⟩ ≫
          DerivedCategory.Q.map
            ((Functor.commShiftIso (integralScalarComplexFunctor l E L ι Y)
              (self := eC) m).hom.app P.obj) ≫
          (DerivedCategory.Q.commShiftIso m).hom.app
            ((integralScalarComplexFunctor l E L ι Y).obj P.obj) := by
  let := good_stable l E Y
  let := eC
  let G := integralOperationsGoodComplex l E Y
  let sh (n : ℤ) := G.lift (G.ι ⋙ shiftFunctor _ n)
    (fun X ↦ G.le_shift n _ X.property)
  let shi (n : ℤ) := G.liftCompιIso (G.ι ⋙ shiftFunctor _ n)
    (fun X ↦ G.le_shift n _ X.property)
  let := G.fullyFaithfulι.hasShift sh shi
  let : G.ι.CommShift ℤ :=
    Functor.CommShift.ofHasShiftOfFullyFaithful G.fullyFaithfulι sh shi
  have : (integralOperationsGoodLocalization l E Y).EssSurj :=
    goodLocalization_essSurj l E Y
  have : ((Functor.whiskeringLeft _ _
      (DerivedCategory (integralTowerModules l L Y))).obj
      (integralOperationsGoodLocalization l E Y)).Full := good_whisker_full l E Y _
  have : ((Functor.whiskeringLeft _ _
      (DerivedCategory (integralTowerModules l L Y))).obj
      (integralOperationsGoodLocalization l E Y)).Faithful :=
    whiskeringLeft_faithful (integralOperationsGoodLocalization l E Y)
  have : ((Functor.whiskeringLeft _ _
      (DerivedCategory (integralTowerModules l L Y))).obj
      ((integralOperationsGoodComplex l E Y).ι ⋙ DerivedCategory.Q)).Full := by
    change ((Functor.whiskeringLeft _ _
      (DerivedCategory (integralTowerModules l L Y))).obj
      (integralOperationsGoodLocalization l E Y)).Full
    infer_instance
  have : ((Functor.whiskeringLeft _ _
      (DerivedCategory (integralTowerModules l L Y))).obj
      ((integralOperationsGoodComplex l E Y).ι ⋙ DerivedCategory.Q)).Faithful := by
    change ((Functor.whiskeringLeft _ _
      (DerivedCategory (integralTowerModules l L Y))).obj
      (integralOperationsGoodLocalization l E Y)).Faithful
    infer_instance
  obtain ⟨eL, hL⟩ := descentShift
    (B := DerivedCategory (integralTowerModules l L Y))
    ((integralOperationsGoodComplex l E Y).ι ⋙ DerivedCategory.Q)
    ((integralOperationsGoodComplex l E Y).ι ⋙
      integralScalarComplexFunctor l E L ι Y ⋙ DerivedCategory.Q)
    (integralScalarExtensionOfUniverses l E L ι Y)
    (integralScalarExtensionComparisonOfUniverses l E L ι Y)
    (CategoryTheory.Functor.FullyFaithful.ofFullyFaithful _)
  refine ⟨eL, ?_⟩
  intro P m
  refine ⟨good_shift l E Y P.obj P.property m, ?_⟩
  have h := hL m P
  simp only [Functor.commShiftIso_comp_hom_app,
    Functor.commShiftIso_comp_inv_app] at h
  have hi := Functor.shiftFunctorIso_ofHasShiftOfFullyFaithful G.fullyFaithfulι sh shi m
  rw [hi] at h
  simp only [shi, ObjectProperty.liftCompιIso, Iso.refl_hom, Iso.refl_inv,
    NatTrans.id_app] at h
  erw [DerivedCategory.Q.map_id, Category.comp_id,
    (integralScalarComplexFunctor l E L ι Y ⋙ DerivedCategory.Q).map_id,
    Category.id_comp] at h
  exact h

end WeilConjectures
