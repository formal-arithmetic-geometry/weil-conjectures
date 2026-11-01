/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.Ringed.RingedDerivedRestrictionGeneralSupplement
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
public import Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.CategoryTheory.AugmentedCechLocalOrthogonality
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Triangulated.Subcategory
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import Mathlib.CategoryTheory.Triangulated.Orthogonal
import all WeilConjectures.ProperBaseChange.RingedLocalizationFactorTensorAugmentation
import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import all WeilConjectures.Algebra.Category.ModuleCat.Presheaf.SheafificationTensor
public import WeilConjectures.CategoryTheory.DerivedCategory.BoundedComplexTriangulatedDevissage
public import WeilConjectures.CategoryTheory.RingedExtendedCech
public import WeilConjectures.CategoryTheory.RingedIdealGenerators
public import WeilConjectures.CategoryTheory.RingedSiteModules

/-! # Independence of augmented extended Cech complexes from generators

Source: Stacks Project, algebraization.tex, Tag 099E, lemma-global-extended-cech-complex;
dualizing.tex, Tag 0A6R, lemma-local-cohomology-adjoint. The ringed-site
tensor-filtration proof is the agent adaptation recorded in the DAG.
(blueprint: lem-weil-pbc-augmented-cech-generator-independence).
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u w

open CategoryTheory CategoryTheory.Limits Opposite
open scoped ZeroObject

namespace CategoryTheory

private theorem augmented_iso_of_colocal
    {D : Type*} [Category D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    (P : ObjectProperty D) [P.IsTriangulated] {X Y R : D}
    (a : X ⟶ R) (b : Y ⟶ R) (ha : P.trW a) (hb : P.trW b)
    (hX : P.leftOrthogonal X) (hY : P.leftOrthogonal Y) :
    ∃ e : X ≅ Y, e.hom ≫ b = a := by
  have hX' : P.trW.isColocal X := by
    rwa [ObjectProperty.isColocal_trW P]
  have hY' : P.trW.isColocal Y := by
    rwa [ObjectProperty.isColocal_trW P]
  obtain ⟨f, hf⟩ := (hX' b hb).surjective a
  obtain ⟨g, hg⟩ := (hY' a ha).surjective b
  refine ⟨⟨f, g, ?_, ?_⟩, hf⟩
  · apply (hX' a ha).injective
    simp only [Category.assoc, hg, hf, Category.id_comp]
  · apply (hY' b hb).injective
    simp only [Category.assoc, hf, hg, Category.id_comp]

@[instance_reducible]
private noncomputable instance moduleMonoidal : MonoidalCategory
    (ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)) :=
  SheafOfModules.monoidalCategory O

private noncomputable instance moduleSymmetric : SymmetricCategory
    (ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)) :=
  SheafOfModules.symmetricCategory O

private noncomputable instance moduleMonoidalPreadditive : MonoidalPreadditive
    (ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)) :=
  (SheafOfModules.tensorClosed O).1.some

private noncomputable instance moduleMonoidalClosed : MonoidalClosed
    (ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)) :=
  (SheafOfModules.tensorClosed O).2.1.some

section TensorFiltration

open MonoidalCategory

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
  (O : Sheaf J CommRingCat.{u})

private noncomputable def moduleScalar
    (s : (O.obj ⋙ forget CommRingCat).sections)
    (M : ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)) :
    M ⟶ M :=
  ⟨PresheafOfModules.sectionsSMul M.val ⟨s.val, s.property⟩⟩

private theorem moduleScalar_sheafify
    (s : (O.obj ⋙ forget CommRingCat).sections)
    (M : PresheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O).obj) :
    (PresheafOfModules.sheafification
        (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O).obj)).map
        (PresheafOfModules.sectionsSMul M ⟨s.val, s.property⟩) =
      moduleScalar O s ((PresheafOfModules.sheafification
        (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O).obj)).obj M) := by
  let adj := PresheafOfModules.sheafificationAdjunction
    (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O).obj)
  apply (adj.homEquiv M _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  change adj.unit.app M ≫ _ =
    adj.unit.app M ≫ PresheafOfModules.sectionsSMul _ ⟨s.val, s.property⟩
  rw [PresheafOfModules.sectionsSMul_naturality]
  exact (adj.unit.naturality _).symm

private theorem moduleScalar_tensor
    (s : (O.obj ⋙ forget CommRingCat).sections)
    (M N : ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)) :
    M ◁ moduleScalar O s N = moduleScalar O s (M ⊗ N) := by
  let adj := PresheafOfModules.sheafificationAdjunction
    (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O).obj)
  apply (cancel_epi (SheafOfModules.tensorObjIsoSheafification M N).inv).mp
  apply (adj.homEquiv (M.val ⊗ N.val) (M ⊗ N)).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  change PresheafOfModules.tensorPure M N ≫ (M ◁ moduleScalar O s N).val =
    PresheafOfModules.tensorPure M N ≫
      PresheafOfModules.sectionsSMul (M ⊗ N).val ⟨s.val, s.property⟩
  have hn := PresheafOfModules.tensorPure_natural (𝟙 M) (moduleScalar O s N)
  simp only [tensorHom_def, id_whiskerRight, Category.id_comp] at hn
  rw [hn, PresheafOfModules.sectionsSMul_naturality]
  congr 1
  apply PresheafOfModules.hom_ext
  intro X
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro x y
  change x ⊗ₜ[O.obj.obj X] (@SMul.smul (O.obj.obj X) _ _ (s.val X) y) =
    @SMul.smul (O.obj.obj X) _ _ (s.val X) (x ⊗ₜ[O.obj.obj X] y)
  exact TensorProduct.tmul_smul _ _ _

private theorem localization_scalar_iso (s : (O.obj ⋙ forget CommRingCat).sections) :
    IsIso (moduleScalar O s (ringedSectionLocalization O s)) := by
  let M := ringedSectionLocalizationPresheaf O s
  let t := PresheafOfModules.sectionsSMul M ⟨s.val, s.property⟩
  have hi (X : Cᵒᵖ) : IsIso (t.app X) := by
    apply (ConcreteCategory.isIso_iff_bijective _).mpr
    change Function.Bijective (fun x : ringedSectionLocalizationCarrier O s X ↦
      @SMul.smul (O.obj.obj X) _ _ (s.val X) x)
    have hu := IsUnit.isUnit_iff_mulLeft_bijective.mp
      (IsLocalization.Away.algebraMap_isUnit (R := O.obj.obj X) (s.val X)
        (S := ringedSectionLocalizationCarrier O s X))
    convert hu using 1
    funext x
    exact Algebra.smul_def (R := O.obj.obj X)
      (A := ringedSectionLocalizationCarrier O s X) (s.val X) x
  let e : M ≅ M := PresheafOfModules.isoMk (fun X ↦ asIso (t.app X))
    (fun {_ _} f ↦ t.naturality f)
  have he : e.hom = t := rfl
  have : IsIso t := he ▸ inferInstance
  dsimp only [ringedSectionLocalization]
  rw [← moduleScalar_sheafify]
  infer_instance

private theorem localization_tensor_scalar_bijective
    (s : (O.obj ⋙ forget CommRingCat).sections)
    (M : ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))
    (X : Cᵒᵖ) :
    Function.Bijective (fun x : (M ⊗ ringedSectionLocalization O s).val.obj X ↦
      @SMul.smul (O.obj.obj X) _ _ (s.val X) x) := by
  have := localization_scalar_iso O s
  have ht : IsIso (moduleScalar O s (M ⊗ ringedSectionLocalization O s)) := by
    rw [← moduleScalar_tensor]
    infer_instance
  let R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj O
  let F := SheafOfModules.forget R ⋙ PresheafOfModules.evaluation R.obj X
  exact (ConcreteCategory.isIso_iff_bijective
    (F.map (moduleScalar O s (M ⊗ ringedSectionLocalization O s)))).mp inferInstance

private theorem cech_bounds (r : ℕ)
    (b : Fin r → (O.obj ⋙ forget CommRingCat).sections) :
    (ringedExtendedCech O r b).1.IsStrictlyGE 0 ∧
      (ringedExtendedCech O r b).1.IsStrictlyLE r := by
  induction r with
  | zero =>
    constructor <;> dsimp [ringedExtendedCech, ringedSiteRingComplex] <;> infer_instance
  | succ r ih =>
    let L := ringedLocalizationTwoTerm O (b 0)
    let K := (ringedExtendedCech O r (fun i ↦ b i.succ)).1
    let := (ih (fun i ↦ b i.succ)).1
    let := (ih (fun i ↦ b i.succ)).2
    let : L.IsStrictlyGE 0 := (CochainComplex.isStrictlyGE_iff L 0).mpr (by
      intro n hn
      change IsZero (ringedLocalizationTwoTermX O (b 0) n)
      simp only [ringedLocalizationTwoTermX, if_neg (by omega : n ≠ 0),
        if_neg (by omega : n ≠ 1)]
      exact isZero_zero _)
    let : L.IsStrictlyLE 1 := (CochainComplex.isStrictlyLE_iff L 1).mpr (by
      intro n hn
      change IsZero (ringedLocalizationTwoTermX O (b 0) n)
      simp only [ringedLocalizationTwoTermX, if_neg (by omega : n ≠ 0),
        if_neg (by omega : n ≠ 1)]
      exact isZero_zero _)
    constructor
    · exact CochainComplex.isStrictlyGE_tensorObj L K 0 0
    · change CochainComplex.IsStrictlyLE (HomologicalComplex.tensorObj L K)
        ((r + 1 : ℕ) : ℤ)
      rw [show ((r + 1 : ℕ) : ℤ) = 1 + (r : ℤ) by omega]
      exact CochainComplex.isStrictlyLE_tensorObj L K 1 r

variable [HasDerivedCategory.{w} (ringedSiteModules.{u}
  ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))]

private theorem factor_projection_trW
    (P : ObjectProperty (ringedSiteDerived O)) [P.IsTriangulated]
    [P.IsClosedUnderIsomorphisms]
    (K : ringedSiteComplex O) (a b : ℤ)
    (hK : ∀ n : ℤ, n < a ∨ b < n → IsZero (K.X n))
    (s : (O.obj ⋙ forget CommRingCat).sections)
    (hP : ∀ M : ringedSiteModules.{u}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O),
      P ((DerivedCategory.singleFunctor _ 0).obj (M ⊗ ringedSectionLocalization O s))) :
    P.trW (DerivedCategory.Q.map
      (HomologicalComplex.tensorHom (𝟙 K) (ringedLocalizationTwoTermAugmentation O s))) := by
  let A := ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)
  let S := ringedSectionLocalization O s
  let T := ((curriedTensor A).map₂CochainComplex).obj K
  let E := ShortComplex.mk (localization_inclusion O s)
    (ringedLocalizationTwoTermAugmentation O s) (localization_inclusion_augmentation O s)
  have hE : (E.map T).ShortExact := tensor_split_exact K E (localization_split O s)
  let N := ((tensorRight S).mapHomologicalComplex (.up ℤ)).obj K
  have hN : P (DerivedCategory.Q.obj N) := by
    apply bounded_complex_mem_triangulated P N a b
    · intro n hn
      exact (tensorRight S).map_isZero (hK n hn)
    · intro n _ _
      exact hP (K.X n)
  let eS : (HomologicalComplex.single A (.up ℤ) 1).obj S ≅
      ((HomologicalComplex.single A (.up ℤ) 0).obj S)⟦(-1 : ℤ)⟧ :=
    (((CochainComplex.singleFunctors A).shiftIso (-1) 1 0 (by omega)).app S).symm
  let e : (E.map T).X₁ ≅ N⟦(-1 : ℤ)⟧ :=
    T.mapIso eS ≪≫
      CochainComplex.mapBifunctorShift₂Iso K
        ((HomologicalComplex.single A (.up ℤ) 0).obj S) (curriedTensor A) (-1) ≪≫
      (shiftFunctor _ (-1 : ℤ)).mapIso
        (CochainComplex.mapBifunctorSingle₂Iso (curriedTensor A) S K)
  have hk : P (DerivedCategory.Q.obj (E.map T).X₁) :=
    P.prop_of_iso (DerivedCategory.Q.mapIso e ≪≫
      (DerivedCategory.Q.commShiftIso (-1)).app N).symm (P.le_shift (-1) _ hN)
  exact ObjectProperty.trW.mk' P (DerivedCategory.triangleOfSES_distinguished hE) hk

private theorem cech_augmentation_trW
    (P : ObjectProperty (ringedSiteDerived O)) [P.IsTriangulated]
    [P.IsClosedUnderIsomorphisms] (r : ℕ)
    (b : Fin r → (O.obj ⋙ forget CommRingCat).sections)
    (hP : ∀ (i : Fin r) (M : ringedSiteModules.{u}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)),
      P ((DerivedCategory.singleFunctor _ 0).obj (M ⊗ ringedSectionLocalization O (b i)))) :
    P.trW (DerivedCategory.Q.map (ringedExtendedCech O r b).2) := by
  induction r with
  | zero =>
    change P.trW (DerivedCategory.Q.map (𝟙 _))
    rw [Functor.map_id]
    exact P.trW.id_mem _
  | succ r ih =>
    let K := (ringedExtendedCech O r (fun i ↦ b i.succ)).1
    let L := ringedLocalizationTwoTerm O (b 0)
    let f := ringedLocalizationTwoTermAugmentation O (b 0)
    let g := (ringedExtendedCech O r (fun i ↦ b i.succ)).2
    have hK : ∀ n : ℤ, n < 0 ∨ (r : ℤ) < n → IsZero (K.X n) := by
      let := (cech_bounds O r (fun i ↦ b i.succ)).1
      let := (cech_bounds O r (fun i ↦ b i.succ)).2
      intro n hn
      rcases hn with hn | hn
      · exact K.isZero_of_isStrictlyGE 0 n hn
      · exact K.isZero_of_isStrictlyLE r n hn
    have hf := factor_projection_trW O P K 0 r hK (b 0) (hP 0)
    have hg := ih (fun i ↦ b i.succ) (fun i ↦ hP i.succ)
    have hfirst : P.trW (DerivedCategory.Q.map (f ▷ K)) := by
      have heq : f ▷ K = (β_ L K).hom ≫ (K ◁ f) ≫
          (β_ (ringedSiteRingComplex O) K).inv := by
        rw [← Category.assoc, ← BraidedCategory.braiding_naturality_left, Category.assoc,
          Iso.hom_inv_id, Category.comp_id]
      rw [heq, Functor.map_comp, Functor.map_comp]
      exact P.trW.comp_mem _ _ (P.trW_of_isIso _)
        (P.trW.comp_mem _ _ hf (P.trW_of_isIso _))
    have hsecond : P.trW (DerivedCategory.Q.map
        (ringedSiteRingComplex O ◁ g ≫ (λ_ (ringedSiteRingComplex O)).hom)) := by
      change P.trW (DerivedCategory.Q.map
        ((𝟙_ (ringedSiteComplex O)) ◁ g ≫ (λ_ (ringedSiteRingComplex O)).hom))
      rw [leftUnitor_naturality, Functor.map_comp]
      exact P.trW.comp_mem _ _ (P.trW_of_isIso _) hg
    change P.trW (DerivedCategory.Q.map
      (HomologicalComplex.tensorHom f g ≫
        (HomologicalComplex.leftUnitor (ringedSiteRingComplex O)).hom))
    change P.trW (DerivedCategory.Q.map ((f ⊗ₘ g) ≫ (λ_ (ringedSiteRingComplex O)).hom))
    rw [tensorHom_def, Category.assoc, Functor.map_comp]
    exact P.trW.comp_mem _ _ hfirst hsecond

private instance localizationClass_iso (U : C) :
    (ringedIdealLocalizationTriangulated O I ι U).IsClosedUnderIsomorphisms where
  of_iso e h P hP hT hgen := by
    let := hP
    exact P.prop_of_iso e (h P hP hT hgen)

private instance localizationClass_triangulated (U : C) :
    (ringedIdealLocalizationTriangulated O I ι U).IsTriangulated where
  exists_zero := ⟨0, isZero_zero _, fun P hP hT _ ↦ by
    let := hP
    let := hT
    exact P.prop_zero⟩
  isStableUnderShiftBy n := ⟨fun E h P hP hT hgen ↦ by
    let := hT
    exact P.le_shift n E (h P hP hT hgen)⟩
  ext₂' T hT h₁ h₃ := by
    apply ObjectProperty.le_isoClosure
    intro P hP hPT hgen
    let := hP
    let := hPT
    exact P.ext_of_isTriangulatedClosed₂ T hT
      (h₁ P hP hPT hgen) (h₃ P hP hPT hgen)

end TensorFiltration

section LocalizationClass

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
  (O : Sheaf J CommRingCat.{u})
  [∀ V : C, HasDerivedCategory.{w} (ringedSiteModules.{u}
    ((sheafCompose (J.over V) (forget₂ CommRingCat RingCat)).obj (O.over V)))]
  (I : ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))
  (ι : I ⟶ SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))

private theorem localizationClass_restrict {U V : C} (a : V ⟶ U)
    (E : ringedSiteDerived (O.over U))
    (hE : ringedIdealLocalizationTriangulated O I ι U E) :
    ringedIdealLocalizationTriangulated O I ι V
      ((ringedKoszulDerivedOverMap O a).obj E) := by
  intro P hP hT hgen
  let := hP
  let := hT
  let (W : C) : HasDerivedCategory.{w} (SheafOfModules.{u}
      (((sheafCompose J (forget₂ CommRingCat RingCat)).obj O).over W)) :=
    inferInstanceAs (HasDerivedCategory.{w} (ringedSiteModules.{u}
      ((sheafCompose (J.over W) (forget₂ CommRingCat RingCat)).obj (O.over W))))
  let F := SheafOfModules.overMap.{u}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O) a
  let D := F.mapDerivedCategory
  apply hE (P.inverseImage D) inferInstance inferInstance
  intro M x hx
  apply P.prop_of_iso ((F.mapDerivedCategorySingleFunctor 0).app M).symm
  apply hgen (F.obj M) (I.val.map a.op x)
  intro W b
  have heq : O.obj.map b.op (ι.val.app (op V) (I.val.map a.op x)) =
      O.obj.map (b ≫ a).op (ι.val.app (op U) x) := by
    have hn := congrArg (fun t ↦ t x) (ι.val.naturality a.op)
    change ι.val.app (op V) (I.val.map a.op x) =
      O.obj.map a.op (ι.val.app (op U) x) at hn
    rw [hn, op_comp, O.obj.map_comp]
    rfl
  change Function.Bijective (fun m : M.val.obj (op (Over.mk (b ≫ a))) ↦
    O.obj.map b.op (ι.val.app (op V) (I.val.map a.op x)) • m)
  rw [heq]
  exact hx W (b ≫ a)

private noncomputable def overMapIdIso (U : C) :
    SheafOfModules.overMap.{u}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O) (𝟙 U) ≅ 𝟭 _ := by
  let R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj O
  exact SheafOfModules.pushforwardNatIso
      (Sheaf.pushforwardOverMapIso R (𝟙 U)).inv (Over.mapId U).symm ≪≫
    SheafOfModules.pushforwardCongr (by ext X x; simp; rfl) ≪≫
    SheafOfModules.pushforwardId (R.over U)

private noncomputable def derivedOverMapIdIso (U : C) :
    ringedKoszulDerivedOverMap O (𝟙 U) ≅ 𝟭 _ := by
  let : HasDerivedCategory.{w} (SheafOfModules.{u}
      (((sheafCompose J (forget₂ CommRingCat RingCat)).obj O).over U)) :=
    inferInstanceAs (HasDerivedCategory.{w} (ringedSiteModules.{u}
      ((sheafCompose (J.over U) (forget₂ CommRingCat RingCat)).obj (O.over U))))
  exact Functor.mapDerivedCategoryNatIso (overMapIdIso O U) ≪≫
    Functor.mapDerivedCategoryIdIso _

private theorem cech_leftOrthogonal [Mono ι] [I.IsFiniteType]
    (U : C) (r : ℕ) (f : Fin r → O.obj.obj (op U))
    (hf : IsRingedIdealGeneratingList O I ι U r f) :
    (ringedIdealLocalizationTriangulated O I ι U).leftOrthogonal
      (DerivedCategory.Q.obj
        (ringedExtendedCech (O.over U) r (fun i ↦ ringedSliceSection O U (f i))).1) := by
  intro E t hE
  have hlocal : ∀ (V : C) (a : V ⟶ U), ∃ S : Sieve V, S ∈ J V ∧
      ∀ (W : C) (b : W ⟶ V), S b →
        ringedIdealLocalizationTriangulated O I ι W
          ((ringedKoszulDerivedOverMap O (b ≫ a)).obj E) := by
    intro V a
    exact ⟨⊤, J.top_mem V, fun W b _ ↦ localizationClass_restrict O I ι (b ≫ a) E hE⟩
  have h := ringed_augmented_cech_local_orthogonality O I ι U r f hf E hlocal U (𝟙 U) 0
  let F := ringedKoszulDerivedOverMap O (𝟙 U)
  let e := derivedOverMapIdIso O U
  have ht : F.map t ≫ (shiftFunctorZero _ ℤ).inv.app (F.obj E) = 0 :=
    h.elim _ _
  have hmap : F.map t = 0 := by
    simpa only [Category.assoc, Iso.inv_hom_id_app, Functor.id_obj, Category.comp_id,
      zero_comp] using
      congrArg (fun z ↦ z ≫ (shiftFunctorZero _ ℤ).hom.app (F.obj E)) ht
  have hn := e.hom.naturality t
  change F.map t ≫ e.hom.app E = e.hom.app _ ≫ t at hn
  rw [hmap, zero_comp] at hn
  exact (cancel_epi (e.hom.app _)).mp (by simpa using hn.symm)

omit [∀ V : C, HasDerivedCategory.{w} (ringedSiteModules.{u}
    ((sheafCompose (J.over V) (forget₂ CommRingCat RingCat)).obj (O.over V)))] in
private theorem generator_mem (U : C) (r : ℕ) (f : Fin r → O.obj.obj (op U))
    (hf : IsRingedIdealGeneratingList O I ι U r f) (i : Fin r) :
    ∃ x : I.val.obj (op U), ι.val.app (op U) x = f i := by
  obtain ⟨σ, e, he⟩ := hf
  refine ⟨(σ.s (e.symm i)).val (op (Over.mk (𝟙 U))), ?_⟩
  have h := he (e.symm i)
  change ι.val.app (op U) ((σ.s (e.symm i)).val (op (Over.mk (𝟙 U)))) =
    f (e (e.symm i)) at h
  simpa only [Equiv.apply_symm_apply] using h

private theorem cech_augmentation_localizationClass (U : C) (r : ℕ)
    (f : Fin r → O.obj.obj (op U))
    (hf : IsRingedIdealGeneratingList O I ι U r f) :
    (ringedIdealLocalizationTriangulated O I ι U).trW
      (DerivedCategory.Q.map
        (ringedExtendedCech (O.over U) r (fun i ↦ ringedSliceSection O U (f i))).2) := by
  apply cech_augmentation_trW (O.over U)
  intro i M
  obtain ⟨x, hx⟩ := generator_mem O I ι U r f hf i
  intro P hP hT hgen
  apply hgen _ x
  intro W a
  rw [hx]
  exact localization_tensor_scalar_bijective (O.over U)
    (ringedSliceSection O U (f i)) M (op (Over.mk a))

end LocalizationClass

/-- Two finite lists generating the same ideal sheaf give isomorphic extended localization
Cech objects, preserving their actual augmentations to the ring in degree zero.
Source: Stacks Project, algebraization.tex, Tag 099E, lemma-global-extended-cech-complex;
dualizing.tex, Tag 0A6R, lemma-local-cohomology-adjoint.
(blueprint: lem-weil-pbc-augmented-cech-generator-independence).

Proof:
1. The localization class in the local-orthogonality theorem is strictly full and
   triangulated. Exact restriction preserves it: pull back a testing triangulated
   class along restriction and use compatibility of restriction with single complexes.
2. A global section acts invertibly on its localization presheaf, hence on its
   sheafification. Tensoring with any module preserves this scalar isomorphism, as
   checked on pure tensors after the sheafification adjunction. Each specified
   generator is the image of a section of I, obtained by evaluation at the identity
   of the slice, so these localized tensor modules belong to the localization class.
3. The factor sequence O[1/s][-1] -> [O -> O[1/s]] -> O[0] is degreewise split.
   Tensor it with a bounded complex K. Its kernel is (K tensor O[1/s])[-1];
   bounded-complex devissage puts this kernel in the localization class when every
   (K^n tensor O[1/s])[0] belongs to it. The associated short-exact-sequence triangle
   makes the tensor projection a morphism whose cone lies in that class.
4. Induct on the actual ordered tensor definition of the Cech complex. The empty
   list has the identity augmentation. In the successor step use the braiding to
   apply step 3 to the first factor; compose with the tail augmentation, using
   naturality of the left unitor. Thus both augmentations have cones in the class.
5. Restriction stability verifies the local-orthogonality hypothesis using maximal
   covering sieves. Restriction along the identity and shift zero are isomorphic
   to the identity, so both Cech objects lie in the class's left orthogonal.
   Mathlib's ObjectProperty.isColocal_trW then says that postcomposition by either
   augmentation induces bijections on morphisms from either Cech object.
6. Lift each augmentation uniquely through the other. The composites and the
   identities have the same augmentations, so injectivity makes the two lifts
   inverse. The covering-sieve equality hypothesis is retained, though unnecessary.
   The empty list, zero generators, and the zero ring require no exceptions. -/
theorem ringed_augmented_cech_generator_independence
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u})
    [∀ V : C, HasDerivedCategory.{w} (ringedSiteModules.{u}
      ((sheafCompose (J.over V) (forget₂ CommRingCat RingCat)).obj (O.over V)))]
    (I : ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))
    (ι : I ⟶ SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))
    [Mono ι] [I.IsFiniteType]
    (U : C) (r s : ℕ) (f : Fin r → O.obj.obj (op U)) (g : Fin s → O.obj.obj (op U))
    (hf : IsRingedIdealGeneratingList O I ι U r f)
    (hg : IsRingedIdealGeneratingList O I ι U s g)
    (hlocal : ∃ S : Sieve U, S ∈ J U ∧ ∀ (V : C) (k : V ⟶ U), S k →
      Ideal.span (Set.range (fun i : Fin r ↦ O.obj.map k.op (f i))) =
        Ideal.span (Set.range (fun j : Fin s ↦ O.obj.map k.op (g j)))) :
    ∃ e : DerivedCategory.Q.obj
        (ringedExtendedCech (O.over U) r (fun i ↦ ringedSliceSection O U (f i))).1 ≅
        DerivedCategory.Q.obj
          (ringedExtendedCech (O.over U) s (fun j ↦ ringedSliceSection O U (g j))).1,
      e.hom ≫ DerivedCategory.Q.map
          (ringedExtendedCech (O.over U) s (fun j ↦ ringedSliceSection O U (g j))).2 =
        DerivedCategory.Q.map
          (ringedExtendedCech (O.over U) r (fun i ↦ ringedSliceSection O U (f i))).2 := by
  have _ := hlocal
  let P := ringedIdealLocalizationTriangulated O I ι U
  exact augmented_iso_of_colocal P _ _
    (cech_augmentation_localizationClass O I ι U r f hf)
    (cech_augmentation_localizationClass O I ι U s g hg)
    (cech_leftOrthogonal O I ι U r f hf)
    (cech_leftOrthogonal O I ι U s g hg)

end CategoryTheory
