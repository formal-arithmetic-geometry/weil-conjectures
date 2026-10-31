/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.RingTheory.Localization.Away.Basic
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
public import Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Homology.HomComplex
public import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationIsIso
public import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationComm
public import WeilConjectures.Algebra.Homology.HomComplexComponents
public import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationNaturality
public import WeilConjectures.ProEtaleCoefficients.RingedStrictTowerHomotopyLimit
public import WeilConjectures.CategoryTheory.Ringed.RingedInternalHomExactRestrictionSupplement
public import Mathlib.Algebra.Homology.Double
public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.RingTheory.Ideal.Span
import all WeilConjectures.ProperBaseChange.RingedGeneratingListsLocalEquality
import all WeilConjectures.ProperBaseChange.RingedAugmentedCechRestriction
import WeilConjectures.ProperBaseChange.RingedLocalizationFactorRestriction
import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import WeilConjectures.CategoryTheory.AugmentedCechGeneratorIndependence

/-! # Augmented comparisons for two generating lists on a common slice

Source: Stacks Project, algebraization.tex, Tag 099E, and sites-cohomology.tex, Tag 08JB.
(blueprint: lem-weil-pbc-augmented-cech-common-slice-comparison).
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
namespace CategoryTheory

private theorem sliceCalculation
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u})
    [∀ U : C, HasDerivedCategory.{w} (SheafOfModules.{u}
      ((sheafCompose (J.over U) (forget₂ CommRingCat RingCat)).obj (O.over U)))]
    (U V : C) (f : V ⟶ U) (r : ℕ)
    (b : Fin r → ((O.over U).obj ⋙ forget CommRingCat).sections) :
    Nonempty
      (Arrow.mk ((ringedKoszulDerivedOverMap O f).map
          (DerivedCategory.Q.map (ringedExtendedCech (O.over U) r b).2)) ≅
        Arrow.mk (DerivedCategory.Q.map
          (ringedExtendedCech (O.over V) r
            (fun i ↦ LocalizationRHom.restrictedSection (K := J.over V)
              (L := J.over U) (Over.map f) (O.over U) (b i))).2)) := by
  let R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj O
  let (X : C) : HasDerivedCategory.{w} (SheafOfModules.{u}
      (((sheafCompose J (forget₂ CommRingCat RingCat)).obj O).over X)) :=
    inferInstanceAs (HasDerivedCategory.{w} (SheafOfModules.{u}
      ((sheafCompose (J.over X) (forget₂ CommRingCat RingCat)).obj (O.over X))))
  let : HasDerivedCategory.{w} (SheafOfModules.{u}
      ((sheafCompose (J.over V) (forget₂ CommRingCat RingCat)).obj
        (((Over.map f).sheafPushforwardContinuous CommRingCat
          (J.over V) (J.over U)).obj (O.over U)))) :=
    inferInstanceAs (HasDerivedCategory.{w} (SheafOfModules.{u}
      ((sheafCompose (J.over V) (forget₂ CommRingCat RingCat)).obj (O.over V))))
  let F := SheafOfModules.overMap.{u} R f
  have h := augmentedCechRestriction_of_factors
    (J := J.over V) (K := J.over U) (Over.map f) (O.over U)
      ((exists_ringed_localization_factor_restriction O).2 U V f) r b
  exact ⟨derivedArrowRestriction F (ringedExtendedCech (O.over U) r b).2 ≪≫
    DerivedCategory.Q.mapArrow.mapIso h.some⟩

private theorem sliceSection_restrict
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u}) (U V : C) (a : V ⟶ U)
    (x : O.obj.obj (op U)) :
    LocalizationRHom.restrictedSection (K := J.over V) (L := J.over U)
        (Over.map a) (O.over U) (ringedSliceSection O U x) =
      ringedSliceSection O V (O.obj.map a.op x) := by
  apply Subtype.ext
  funext W
  change O.obj.map (W.unop.hom ≫ a).op x =
    O.obj.map W.unop.hom.op (O.obj.map a.op x)
  rw [op_comp, Functor.map_comp]
  rfl

private theorem sliceListCalculation
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u})
    [∀ U : C, HasDerivedCategory.{w} (SheafOfModules.{u}
      ((sheafCompose (J.over U) (forget₂ CommRingCat RingCat)).obj (O.over U)))]
    (U V : C) (a : V ⟶ U) (r : ℕ) (f : Fin r → O.obj.obj (op U)) :
    Nonempty
      (Arrow.mk ((ringedKoszulDerivedOverMap O a).map
          (DerivedCategory.Q.map (ringedExtendedCech (O.over U) r
            (fun i ↦ ringedSliceSection O U (f i))).2)) ≅
        Arrow.mk (DerivedCategory.Q.map (ringedExtendedCech (O.over V) r
          (fun i ↦ ringedSliceSection O V (O.obj.map a.op (f i)))).2)) := by
  have h := sliceCalculation O U V a r (fun i ↦ ringedSliceSection O U (f i))
  have hs : (fun i : Fin r ↦ LocalizationRHom.restrictedSection
      (K := J.over V) (L := J.over U) (Over.map a) (O.over U)
        (ringedSliceSection O U (f i))) =
      (fun i ↦ ringedSliceSection O V (O.obj.map a.op (f i))) := by
    funext i
    exact sliceSection_restrict O U V a (f i)
  rw [hs] at h
  exact h

end CategoryTheory

namespace CategoryTheory

private theorem overMap_preserves_colimits
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) {U V : C} (f : V ⟶ U) :
    PreservesColimitsOfSize.{u, u} (SheafOfModules.overMap.{u} R f) := by
  let F := SheafOfModules.overMap.{u} R f
  let H := (Over.map f).sheafPushforwardContinuous AddCommGrpCat.{u} (J.over V) (J.over U)
  have : PreservesColimitsOfSize.{u, u} H :=
    ((Over.map f).sheafAdjunctionCocontinuous AddCommGrpCat.{u}
      (J.over V) (J.over U)).leftAdjoint_preservesColimits
  let T := SheafOfModules.toSheaf.{u} (R.over V)
  have : PreservesColimitsOfSize.{u, u} (SheafOfModules.toSheaf.{u} (R.over U)) :=
    { preservesColimitsOfShape := inferInstance }
  have : PreservesColimitsOfSize.{u, u} T :=
    { preservesColimitsOfShape := inferInstance }
  have : PreservesColimitsOfSize.{u, u} (F ⋙ T) := by
    change PreservesColimitsOfSize.{u, u} (SheafOfModules.toSheaf.{u} (R.over U) ⋙ H)
    infer_instance
  have : ReflectsColimitsOfSize.{u, u} T := reflectsColimits_of_reflectsIsomorphisms
  exact preservesColimits_of_reflects_of_preserves F T

private theorem mapped_generator
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) {U V : C} (f : V ⟶ U)
    (M : SheafOfModules.{u} (R.over U)) (σ : M.GeneratingSections) (i : σ.I) :
    let := overMap_preserves_colimits R f
    let F := SheafOfModules.overMap.{u} R f
    (σ.map F (SheafOfModules.overMapUnitIso (R := R) f).symm).s i =
      (F.obj M).unitHomEquiv
        ((SheafOfModules.overMapUnitIso (R := R) f).inv ≫
          F.map (M.unitHomEquiv.symm (σ.s i))) := by
  dsimp only
  apply (SheafOfModules.unitHomEquiv _).symm.injective
  rw [Equiv.symm_apply_apply]
  change (SheafOfModules.unitHomEquiv _).symm
    (SheafOfModules.freeHomEquiv _ _ i) = _
  rw [SheafOfModules.unitHomEquiv_symm_freeHomEquiv_apply]
  dsimp only [SheafOfModules.GeneratingSections.mapFreeHom]
  rw [← Category.assoc, SheafOfModules.ιFree_mapFreeIso_hom, Category.assoc,
    ← Functor.map_comp, ← SheafOfModules.unitHomEquiv_symm_freeHomEquiv_apply]
  congr 2
  exact congrArg M.unitHomEquiv.symm
    (congrFun (M.freeHomEquiv.apply_symm_apply σ.s) i)


private theorem mapped_generator_eval
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) {U V : C} (f : V ⟶ U)
    (M : SheafOfModules.{u} (R.over U)) (σ : M.GeneratingSections) (i : σ.I)
    (W : Over V) :
    let := overMap_preserves_colimits R f
    let F := SheafOfModules.overMap.{u} R f
    ((σ.map F (SheafOfModules.overMapUnitIso (R := R) f).symm).s i).val (op W) =
      (σ.s i).val (op ((Over.map f).obj W)) := by
  dsimp only
  rw [mapped_generator, SheafOfModules.unitHomEquiv_apply_coe]
  change (M.unitHomEquiv.symm (σ.s i)).val.app
    (op ((Over.map f).obj W)) (1 : R.obj.obj (op W.left)) = _
  exact congrArg (fun s ↦ s.val (op ((Over.map f).obj W)))
    (M.unitHomEquiv.apply_symm_apply (σ.s i))


private theorem generatingList_restrict
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u})
    (I : ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))
    (ι : I ⟶ SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))
    (U V : C) (f : V ⟶ U) (r : ℕ) (b : Fin r → O.obj.obj (op U))
    (hb : IsRingedIdealGeneratingList O I ι U r b) :
    IsRingedIdealGeneratingList O I ι V r (fun i ↦ O.obj.map f.op (b i)) := by
  obtain ⟨σ, e, he⟩ := hb
  let R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj O
  let F := SheafOfModules.overMap.{u} R f
  let := overMap_preserves_colimits R f
  let τ := (σ.map F (SheafOfModules.overMapUnitIso (R := R) f).symm).ofEpi
    ((SheafOfModules.overFunctorMap R f).hom.app I)
  refine ⟨τ, e, ?_⟩
  intro i
  change ι.val.app (op V)
    (((σ.map F (SheafOfModules.overMapUnitIso (R := R) f).symm).s i).val
      (op (Over.mk (𝟙 V)))) = O.obj.map f.op (b (e i))
  rw [mapped_generator_eval]
  change ι.val.app (op V) ((σ.s i).val (op (Over.mk (𝟙 V ≫ f)))) = _
  trans ι.val.app (op V) ((σ.s i).val (op (Over.mk f)))
  · exact congrArg (fun t : V ⟶ U ↦
      ι.val.app (op V) ((σ.s i).val (op (Over.mk t)))) (Category.id_comp f)
  · exact generatingList_section_value O I ι U r b σ e he V f i

end CategoryTheory

namespace CategoryTheory

private noncomputable def unitActionIso
    {D : Type*} [Category* D] [MonoidalCategory D]
    (a : 𝟙_ D ≅ 𝟙_ D) (X : D) : X ≅ X :=
  (λ_ X).symm ≪≫ ((tensoringRight D).obj X).mapIso a ≪≫ λ_ X

private theorem unitActionIso_naturality
    {D : Type*} [Category* D] [MonoidalCategory D]
    (a : 𝟙_ D ≅ 𝟙_ D) {X Y : D} (f : X ⟶ Y) :
    (unitActionIso a X).hom ≫ f = f ≫ (unitActionIso a Y).hom := by
  simp only [unitActionIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    Category.assoc]
  change (λ_ X).inv ≫ a.hom ▷ X ≫ (λ_ X).hom ≫ f =
    f ≫ (λ_ Y).inv ≫ a.hom ▷ Y ≫ (λ_ Y).hom
  rw [← leftUnitor_naturality, ← whisker_exchange_assoc,
    leftUnitor_inv_naturality_assoc]

private theorem unitActionIso_unit
    {D : Type*} [Category* D] [MonoidalCategory D]
    (a : 𝟙_ D ≅ 𝟙_ D) : (unitActionIso a (𝟙_ D)).hom = a.hom := by
  have hunit : (λ_ (𝟙_ D)) = (ρ_ (𝟙_ D)) := Iso.ext unitors_equal
  simp only [unitActionIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
  change (λ_ (𝟙_ D)).inv ≫ a.hom ▷ (𝟙_ D) ≫ (λ_ (𝟙_ D)).hom = a.hom
  rw [hunit]
  exact (whiskerRight_id_symm a.hom).symm

private theorem normalize_augmented_arrow
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u})
    [HasDerivedCategory.{w} (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))]
    {X : ringedSiteDerived O} {Y : ringedSiteComplex O}
    (ε : Y ⟶ ringedSiteRingComplex O)
    {Z : ringedSiteDerived O} (v : X ⟶ Z)
    (e : Arrow.mk v ≅ Arrow.mk (DerivedCategory.Q.map ε))
    (r : Z ≅ DerivedCategory.Q.obj (ringedSiteRingComplex O)) :
    ∃ c : X ≅ DerivedCategory.Q.obj Y,
      c.hom ≫ DerivedCategory.Q.map ε = v ≫ r.hom := by
  let M := ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)
  let R := SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)
  let S := DerivedCategory.singleFunctor M 0
  let eL : X ≅ DerivedCategory.Q.obj Y := Arrow.leftFunc.mapIso e
  let eR : Z ≅ DerivedCategory.Q.obj (ringedSiteRingComplex O) := Arrow.rightFunc.mapIso e
  let a : S.obj R ≅ S.obj R := eR.symm ≪≫ r
  let b := (Functor.FullyFaithful.ofFullyFaithful S).preimageIso a
  let bc := (HomologicalComplex.single M (.up ℤ) 0).mapIso b
  let := SheafOfModules.monoidalCategory O
  let d : Y ≅ Y := HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ unitActionIso b (Y.X n))
    (fun n m h ↦ unitActionIso_naturality b (Y.d n m))
  refine ⟨eL ≪≫ DerivedCategory.Q.mapIso d, ?_⟩
  have hd : d.hom ≫ ε = ε ≫ bc.hom := by
    apply HomologicalComplex.hom_ext
    intro n
    change (unitActionIso b (Y.X n)).hom ≫ ε.f n = ε.f n ≫ bc.hom.f n
    rw [unitActionIso_naturality]
    congr 1
    by_cases hn : n = 0
    · subst n
      let e₀ := HomologicalComplex.singleObjXSelf (.up ℤ) 0 R
      apply (cancel_mono e₀.hom).1
      have hn := unitActionIso_naturality b e₀.hom
      have hbunit : (unitActionIso b R).hom = b.hom := unitActionIso_unit (D := M) b
      rw [hbunit] at hn
      simpa only [e₀, bc, Functor.mapIso_hom, HomologicalComplex.single_map_f_self,
        Category.assoc, Iso.inv_hom_id, Category.comp_id] using hn
    · apply (HomologicalComplex.isZero_single_obj_X _ _ _ _ hn).eq_of_tgt
  have hb : DerivedCategory.Q.map bc.hom = a.hom := by
    exact (Functor.FullyFaithful.ofFullyFaithful S).map_preimage a.hom
  have he : eL.hom ≫ DerivedCategory.Q.map ε = v ≫ eR.hom := e.hom.w
  change (eL.hom ≫ DerivedCategory.Q.map d.hom) ≫ DerivedCategory.Q.map ε = v ≫ r.hom
  rw [Category.assoc, ← Functor.map_comp, hd, Functor.map_comp, hb,
    ← Category.assoc, he]
  simp only [a, Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc]

end CategoryTheory

namespace CategoryTheory

/-- Two generating lists on different objects give an augmented comparison on a
common slice whenever their transported section ideals agree on a covering sieve.

Source: Stacks Project, algebraization.tex, Tag 099E, independence of generating ideals;
sites-cohomology.tex, Tag 08JB, exact restriction.
(blueprint: lem-weil-pbc-augmented-cech-common-slice-comparison).

Proof: restrict the lists along Over.map a and Over.map b. Restriction of the
finite free epimorphisms witnessing the generating lists, with the unit and
coproduct comparisons, shows that the entries O(a)(f_i) and O(b)(g_j) still generate
the ideal on W. Naturality of sections identifies restriction of each slice-global
section with the slice section of the corresponding entry on W. Localization of
fractions, module sheafification and finite tensor totalization give arrow
isomorphisms from the two restricted augmentations to these W-list augmentations.
An arbitrary arrow isomorphism need not have the prescribed right component.
Normalize it as follows. Divide its right component into the prescribed canonical
ring comparison, obtaining an automorphism of O_W[0]. Full faithfulness of the
degree-zero single functor lifts it to an automorphism of the unit module. Its
tensor action, conjugated by the left unitors, gives a natural automorphism of
module sheaves and hence of their complexes. Its value on the unit is the given
automorphism by equality of the two unitors. Naturality for the augmentation now
adjusts the left arrow isomorphism to have exactly the prescribed right component.
Apply this to the canonical comparison G_a(rho_U inverse), followed by kappa_a
and rho_W, and similarly for b. The given local equality becomes the hypothesis
of generator independence for the two lists on W; their augmented comparison,
composed with the two normalized restriction comparisons, gives c. Cancel rho_W
to obtain precisely the displayed equation. Empty lists, zero rings and zero and
unit ideals satisfy the same constructions.
-/
theorem augmented_cech_common_slice_comparison
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u})
    [HasDerivedCategory.{w} (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))]
    [∀ U : C, HasDerivedCategory.{w} (ringedSiteModules.{u}
      ((sheafCompose (J.over U) (forget₂ CommRingCat RingCat)).obj (O.over U)))]
    (I : ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))
    (ι : I ⟶ SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))
    [Mono ι] [I.IsFiniteType]
    (U V : C) (r s : ℕ)
    (f : Fin r → O.obj.obj (op U)) (g : Fin s → O.obj.obj (op V))
    (hf : IsRingedIdealGeneratingList O I ι U r f)
    (hg : IsRingedIdealGeneratingList O I ι V s g)
    (W : C) (a : W ⟶ U) (b : W ⟶ V)
    (hlocal : ∃ S : Sieve W, S ∈ J W ∧
      ∀ (T : C) (k : T ⟶ W), S k →
        Ideal.span (Set.range (fun i ↦ O.obj.map (k ≫ a).op (f i))) =
          Ideal.span (Set.range (fun i ↦ O.obj.map (k ≫ b).op (g i)))) :
    ∃ c : (ringedKoszulDerivedOverMap O a).obj
          (DerivedCategory.Q.obj (ringedExtendedCech (O.over U) r
            (fun i ↦ ringedSliceSection O U (f i))).1) ≅
        (ringedKoszulDerivedOverMap O b).obj
          (DerivedCategory.Q.obj (ringedExtendedCech (O.over V) s
            (fun i ↦ ringedSliceSection O V (g i))).1),
      c.hom ≫ (ringedKoszulDerivedOverMap O b).map
          (DerivedCategory.Q.map (ringedExtendedCech (O.over V) s
            (fun i ↦ ringedSliceSection O V (g i))).2 ≫
              (ringedDerivedRingRestrictionIso O V).inv) ≫
            (ringedKoszulDerivedOverComparison O b).hom.app
              (DerivedCategory.Q.obj (ringedSiteRingComplex O)) =
        (ringedKoszulDerivedOverMap O a).map
          (DerivedCategory.Q.map (ringedExtendedCech (O.over U) r
            (fun i ↦ ringedSliceSection O U (f i))).2 ≫
              (ringedDerivedRingRestrictionIso O U).inv) ≫
            (ringedKoszulDerivedOverComparison O a).hom.app
              (DerivedCategory.Q.obj (ringedSiteRingComplex O)) := by
  let fa : Fin r → O.obj.obj (op W) := fun i ↦ O.obj.map a.op (f i)
  let gb : Fin s → O.obj.obj (op W) := fun i ↦ O.obj.map b.op (g i)
  let F := ringedKoszulDerivedOverMap O a
  let G := ringedKoszulDerivedOverMap O b
  let εf := (ringedExtendedCech (O.over U) r
    (fun i ↦ ringedSliceSection O U (f i))).2
  let εg := (ringedExtendedCech (O.over V) s
    (fun i ↦ ringedSliceSection O V (g i))).2
  let εfa := (ringedExtendedCech (O.over W) r
    (fun i ↦ ringedSliceSection O W (fa i))).2
  let εgb := (ringedExtendedCech (O.over W) s
    (fun i ↦ ringedSliceSection O W (gb i))).2
  have hfa : Nonempty (Arrow.mk (F.map (DerivedCategory.Q.map εf)) ≅
      Arrow.mk (DerivedCategory.Q.map εfa)) := by
    exact sliceListCalculation O U W a r f
  have hgb : Nonempty (Arrow.mk (G.map (DerivedCategory.Q.map εg)) ≅
      Arrow.mk (DerivedCategory.Q.map εgb)) := by
    exact sliceListCalculation O V W b s g
  let o := DerivedCategory.Q.obj (ringedSiteRingComplex O)
  let Rf := (F.mapIso (ringedDerivedRingRestrictionIso O U)).symm ≪≫
    (ringedKoszulDerivedOverComparison O a).app o ≪≫ ringedDerivedRingRestrictionIso O W
  let Rg := (G.mapIso (ringedDerivedRingRestrictionIso O V)).symm ≪≫
    (ringedKoszulDerivedOverComparison O b).app o ≪≫ ringedDerivedRingRestrictionIso O W
  obtain ⟨cf, hcf⟩ := normalize_augmented_arrow (O.over W) εfa _ hfa.some Rf
  obtain ⟨cg, hcg⟩ := normalize_augmented_arrow (O.over W) εgb _ hgb.some Rg
  have hf' := generatingList_restrict O I ι U W a r f hf
  have hg' := generatingList_restrict O I ι V W b s g hg
  have hlocal' : ∃ S : Sieve W, S ∈ J W ∧
      ∀ (T : C) (k : T ⟶ W), S k →
        Ideal.span (Set.range (fun i ↦ O.obj.map k.op (fa i))) =
          Ideal.span (Set.range (fun i ↦ O.obj.map k.op (gb i))) := by
    obtain ⟨S, hS, h⟩ := hlocal
    refine ⟨S, hS, ?_⟩
    intro T k hk
    simpa only [fa, gb, op_comp, Functor.map_comp, ConcreteCategory.comp_apply] using h T k hk
  obtain ⟨l, hl⟩ := ringed_augmented_cech_generator_independence O I ι W r s fa gb
    hf' hg' hlocal'
  let c := cf ≪≫ l ≪≫ cg.symm
  refine ⟨c, ?_⟩
  apply (cancel_mono (ringedDerivedRingRestrictionIso O W).hom).1
  have hc : c.hom ≫ G.map (DerivedCategory.Q.map εg) ≫ Rg.hom =
      F.map (DerivedCategory.Q.map εf) ≫ Rf.hom := by
    rw [← hcg]
    simp only [c, Iso.trans_hom, Iso.symm_hom, Category.assoc,
      Iso.inv_hom_id_assoc]
    rw [hl, hcf]
  simpa only [Rf, Rg, F, G, εf, εg, o, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_inv, Functor.map_comp, Iso.app_hom, Category.assoc] using hc

end CategoryTheory
