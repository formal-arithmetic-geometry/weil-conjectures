/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q94
-/
module

public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Homology.KFlat
public import WeilConjectures.Algebra.Homology.HomComplex
public import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
public import Sheaf.Algebra.Homology.RingedSiteZerothHypercohomologyOfUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Adjunction.Basic
import Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients

public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
import all Sheaf.Algebra.Homology.HomComplexGlobalHomotopyOfUniverses
import Sheaf.Algebra.Homology.GlobalTensorHomCochainsOfUniverses
import Sheaf.Algebra.Homology.QuasiIsoHomComplexMapOfUniverses
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
/-! # K-injective models for internal Hom and its derived global sections

Source: Stacks Project, sites-cohomology.tex, Section 08J7 (section-internal-hom),
Lemmas 0A95, 0A96, 08JA and 08J9
(blueprint: lem-sfb-derived-internal-hom-sections-model).

The tensor functor is characterized by its natural total-complex models on K-flat
representatives. The internal Hom is the existing Hom-complex localization. All
representative comparisons are natural isomorphisms, including the full derived
complex of global sections, rather than only its zeroth cohomology.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe c v r w z

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite

namespace CategoryTheory.DerivedInternalHomSectionsModel.GlobalCochains

open CochainComplex HomComplex Limits Preadditive in
@[no_expose]
private noncomputable def externalHomologyIsoDegree
    {D : Type*} [Category* D] [Preadditive D] (A B : CochainComplex D ℤ) (n : ℤ) :
    (HomologicalComplex.homologyFunctor AddCommGrpCat (.up ℤ) n).obj
        (HomComplex A B) ≅ AddCommGrpCat.of
      ((HomotopyCategory.quotient D (.up ℤ)).obj A ⟶
        (HomotopyCategory.quotient D (.up ℤ)).obj (B⟦n⟧)) :=
  (HomComplex.leftHomologyData A B n).homologyIso ≪≫
    (CohomologyClass.homAddEquiv (K := A) (L := B) (n := n)).toAddCommGrpIso

set_option backward.isDefEq.respectTransparency false in
open CochainComplex HomComplex Limits Preadditive in
@[no_expose]
private noncomputable def externalHomologyMapDataDegree
    {D : Type*} [Category* D] [Preadditive D]
    {A A' B B' : CochainComplex D ℤ} (f : A' ⟶ A) (g : B ⟶ B') (n : ℤ) :
    ShortComplex.LeftHomologyMapData
      ((HomologicalComplex.shortComplexFunctor _ _ n).map (externalMap f g))
      (HomComplex.leftHomologyData A B n) (HomComplex.leftHomologyData A' B' n) where
  φK := AddCommGrpCat.ofHom
    { toFun := fun z ↦ (z.precomp f).postcomp g
      map_zero' := by ext; simp
      map_add' := by intros; ext; simp }
  φH := (CohomologyClass.homAddEquiv (K := A) (L := B) (n := n)).toAddCommGrpIso.hom ≫
    (AddCommGrpCat.ofHom
      { toFun := fun a ↦ (HomotopyCategory.quotient D (.up ℤ)).map f ≫ a ≫
          (HomotopyCategory.quotient D (.up ℤ)).map ((shiftFunctor _ n).map g)
        map_zero' := by simp
        map_add' := by intros; simp [comp_add, add_comp] }) ≫
      (CohomologyClass.homAddEquiv (K := A') (L := B') (n := n)).toAddCommGrpIso.inv
  commi := by ext z; rfl
  commf' := by
    rw [← cancel_mono (HomComplex.leftHomologyData A' B' n).i]
    simp only [Category.assoc, ShortComplex.LeftHomologyData.f'_i]
    have hi : AddCommGrpCat.ofHom
        { toFun := fun z : Cocycle A B n ↦ (z.precomp f).postcomp g
          map_zero' := by ext; simp
          map_add' := by intros; ext; simp } ≫
        (HomComplex.leftHomologyData A' B' n).i =
      (HomComplex.leftHomologyData A B n).i ≫ (externalMap f g).f n := by
      ext z
      rfl
    rw [hi, ShortComplex.LeftHomologyData.f'_i_assoc]
    exact ((HomologicalComplex.shortComplexFunctor _ _ n).map
      (externalMap f g)).comm₁₂.symm
  commπ := by
    ext z
    apply (CohomologyClass.homAddEquiv (K := A') (L := B') (n := n)).injective
    change CohomologyClass.homAddEquiv (K := A') (L := B') (n := n)
      ((CohomologyClass.homAddEquiv (K := A') (L := B') (n := n)).symm
      ((HomotopyCategory.quotient D (.up ℤ)).map f ≫
        CohomologyClass.homAddEquiv (K := A) (L := B) (n := n) (CohomologyClass.mk z) ≫
          (HomotopyCategory.quotient D (.up ℤ)).map ((shiftFunctor _ n).map g))) =
      CohomologyClass.homAddEquiv (K := A') (L := B') (n := n)
        (CohomologyClass.mk ((z.precomp f).postcomp g))
    rw [AddEquiv.apply_symm_apply]
    change (HomotopyCategory.quotient D (.up ℤ)).map f ≫
        CohomologyClass.toHom (CohomologyClass.mk z) ≫
          (HomotopyCategory.quotient D (.up ℤ)).map ((shiftFunctor _ n).map g) =
      CohomologyClass.toHom (CohomologyClass.mk ((z.precomp f).postcomp g))
    rw [CohomologyClass.toHom_mk, CohomologyClass.toHom_mk,
      ← Functor.map_comp, ← Functor.map_comp]
    congr 1
    ext p
    simp [Cocycle.equivHomShift_symm_apply, Cocycle.homOf, Cocycle.rightShift,
      Cochain.rightShift_v, Cocycle.precomp, Cocycle.postcomp,
      Cochain.comp_zero_cochain_v, Cochain.zero_cochain_comp_v]

set_option backward.isDefEq.respectTransparency false in
open CochainComplex HomComplex Limits Preadditive in
private lemma externalHomologyIsoDegree_naturality
    {D : Type*} [Category* D] [Preadditive D]
    {A A' B B' : CochainComplex D ℤ} (f : A' ⟶ A) (g : B ⟶ B') (n : ℤ) :
    HomologicalComplex.homologyMap (externalMap f g) n ≫
      (externalHomologyIsoDegree A' B' n).hom =
    (externalHomologyIsoDegree A B n).hom ≫ AddCommGrpCat.ofHom
      { toFun := fun a ↦ (HomotopyCategory.quotient D (.up ℤ)).map f ≫ a ≫
          (HomotopyCategory.quotient D (.up ℤ)).map ((shiftFunctor _ n).map g)
        map_zero' := by simp
        map_add' := by intros; simp [comp_add, add_comp] } := by
  have h := (externalHomologyMapDataDegree f g n).homologyMap_eq
  change HomologicalComplex.homologyMap (externalMap f g) n = _ at h
  rw [h]
  dsimp only [externalHomologyIsoDegree, externalHomologyMapDataDegree]
  simp only [Iso.trans_hom, Category.assoc, Iso.inv_hom_id_assoc]
  ext a
  change CohomologyClass.homAddEquiv (K := A') (L := B') (n := n)
      ((CohomologyClass.homAddEquiv (K := A') (L := B') (n := n)).symm
    ((HomotopyCategory.quotient D (.up ℤ)).map f ≫
      CohomologyClass.homAddEquiv (K := A) (L := B) (n := n)
        ((HomComplex.leftHomologyData A B n).homologyIso.hom a) ≫
        (HomotopyCategory.quotient D (.up ℤ)).map ((shiftFunctor _ n).map g))) = _
  exact AddEquiv.apply_symm_apply _ _

private theorem externalMap_quasiIso
    {D : Type*} [Category* D] [Abelian D] [HasDerivedCategory D]
    {A A' I : CochainComplex D ℤ} (f : A' ⟶ A) [QuasiIso f] [I.IsKInjective] :
    QuasiIso (CategoryTheory.externalMap f (𝟙 I)) := by
  refine ⟨fun n ↦ ?_⟩
  rw [quasiIsoAt_iff_isIso_homologyMap]
  let m := AddCommGrpCat.ofHom
    { toFun := fun a : (HomotopyCategory.quotient D (.up ℤ)).obj A ⟶
          (HomotopyCategory.quotient D (.up ℤ)).obj (I⟦n⟧) ↦
        (HomotopyCategory.quotient D (.up ℤ)).map f ≫ a ≫
          (HomotopyCategory.quotient D (.up ℤ)).map ((shiftFunctor _ n).map (𝟙 I))
      map_zero' := by simp
      map_add' := by intros; simp [Preadditive.comp_add] }
  have : IsIso m := by
    rw [ConcreteCategory.isIso_iff_bijective]
    let q := HomotopyCategory.quotient D (.up ℤ)
    let a := DerivedCategory.Qh.map (q.map f)
    have : IsIso a := by
      change IsIso ((q ⋙ DerivedCategory.Qh).map f)
      exact (NatIso.isIso_map_iff (DerivedCategory.quotientCompQhIso D) f).2 inferInstance
    have hA := CochainComplex.IsKInjective.Qh_map_bijective (q.obj A) (I⟦n⟧)
    have hA' := CochainComplex.IsKInjective.Qh_map_bijective (q.obj A') (I⟦n⟧)
    change Function.Bijective (fun g ↦ q.map f ≫ g ≫
      q.map ((shiftFunctor _ n).map (𝟙 I)))
    simp only [Functor.map_id, Category.comp_id]
    constructor
    · intro g h eq
      apply hA.injective
      apply (cancel_epi a).mp
      simpa only [a, Functor.map_comp] using congrArg DerivedCategory.Qh.map eq
    · intro g
      obtain ⟨h, hh⟩ := hA.surjective (inv a ≫ DerivedCategory.Qh.map g)
      refine ⟨h, hA'.injective ?_⟩
      rw [Functor.map_comp, hh]
      exact IsIso.hom_inv_id_assoc a _
  have : IsIso (HomologicalComplex.homologyMap (externalMap f (𝟙 I)) n ≫
      (externalHomologyIsoDegree A' I n).hom) := by
    rw [externalHomologyIsoDegree_naturality]
    change IsIso ((externalHomologyIsoDegree A I n).hom ≫ m)
    infer_instance
  exact IsIso.of_isIso_comp_right _ (externalHomologyIsoDegree A' I n).hom


end CategoryTheory.DerivedInternalHomSectionsModel.GlobalCochains

namespace CategoryTheory.DerivedInternalHomSectionsModel

variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{max c v r})

/-- The recorded module category, with sections in a universe containing the site.
Source: Stacks, Section 08J7
(blueprint: lem-sfb-derived-internal-hom-sections-model). -/
abbrev Modules := ringedSiteModules.{max c v r}
  ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)

/-- Unbounded cochain complexes in the recorded module category.
Source: Stacks, Section 08J7
(blueprint: lem-sfb-derived-internal-hom-sections-model). -/
abbrev Complexes := CochainComplex (Modules.{c, v, r} R) ℤ

variable [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]

/-- The recorded unbounded derived category, with its chosen morphism universe.
Source: Stacks, Section 08J7
(blueprint: lem-sfb-derived-internal-hom-sections-model). -/
abbrev Derived [HasDerivedCategory.{w} (Modules.{c, v, r} R)] :=
  DerivedCategory (Modules.{c, v, r} R)

/-- Ordinary global sections are morphisms from the unit module sheaf.
Source: Stacks, Section 07A5 and Lemma 08JA
(blueprint: lem-sfb-derived-internal-hom-sections-model). -/
noncomputable abbrev sections : Modules.{c, v, r} R ⥤ AddCommGrpCat.{max c v r} :=
  preadditiveCoyoneda.obj (op (SheafOfModules.unit
    ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)))

variable [HasDerivedCategory.{w} (Modules.{c, v, r} R)]
  [HasDerivedCategory.{z} AddCommGrpCat.{max c v r}]

/-- The full right derived global-sections functor underlying the recorded
zeroth-hypercohomology construction. It uses the same canonical K-injective replacement.
Source: Stacks, Section 07A5 and Lemma 08JA
(blueprint: lem-sfb-derived-internal-hom-sections-model). -/
noncomputable def derivedSections :
    Derived.{c, v, r, w} R ⥤ DerivedCategory.{z} AddCommGrpCat.{max c v r} :=
  letI : IsGrothendieckAbelian.{max c v r} (Modules.{c, v, r} R) :=
    (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{c, v, r}
      J R).1
  (sections.{c, v, r} R).rightDerivedFunctor

/-- The existing internal-Hom bifunctor, in curried form.
Source: Stacks, Section 08J7
(blueprint: lem-sfb-derived-internal-hom-sections-model). -/
noncomputable abbrev internalHom :
    (Derived.{c, v, r, w} R)ᵒᵖ ⥤ Derived.{c, v, r, w} R ⥤ Derived.{c, v, r, w} R :=
  Functor.curry.obj (derivedInternalHomOfUniverses.{c, v, r, w} J R)

/-- The full subcategory of K-injective complexes; no condition on the source is imposed.
Source: Stacks, Definition 070H and Section 08J7
(blueprint: lem-sfb-derived-internal-hom-sections-model). -/
def injectiveProperty : ObjectProperty (Complexes.{c, v, r} R) :=
  fun I ↦ CochainComplex.IsKInjective I

/-- Restrict the recorded derived internal Hom to arbitrary source complexes and
K-injective target complexes.
Source: Stacks, Section 08J7
(blueprint: lem-sfb-derived-internal-hom-sections-model). -/
noncomputable def representedInternalHom :
    (Complexes.{c, v, r} R)ᵒᵖ × (injectiveProperty.{c, v, r} R).FullSubcategory ⥤
      Derived.{c, v, r, w} R :=
  (DerivedCategory.Q.op.prod ((injectiveProperty.{c, v, r} R).ι ⋙ DerivedCategory.Q)) ⋙
    derivedInternalHomOfUniverses.{c, v, r, w} J R

/-- The recorded sheaf Hom complex on the same pairs of representatives.
Source: Stacks, Section 08J7 and Section 0A8X
(blueprint: lem-sfb-derived-internal-hom-sections-model). -/
noncomputable def representativeHom :
    (Complexes.{c, v, r} R)ᵒᵖ × (injectiveProperty.{c, v, r} R).FullSubcategory ⥤
      Complexes.{c, v, r} R :=
  (𝟭 (Complexes.{c, v, r} R)ᵒᵖ).prod (injectiveProperty.{c, v, r} R).ι ⋙
    Functor.uncurry.obj (homComplexFunctor (R := R))

/-- The ordinary complex of global Hom cochains, functorially in both representatives.
Source: Stacks, Section 0A8X, equation-global-cohomology-hom-complex
(blueprint: lem-sfb-derived-internal-hom-sections-model). -/
noncomputable def globalHom :
    (Complexes.{c, v, r} R)ᵒᵖ × (injectiveProperty.{c, v, r} R).FullSubcategory ⥤
      CochainComplex AddCommGrpCat.{max c v r} ℤ :=
  representativeHom.{c, v, r} R ⋙ (sections.{c, v, r} R).mapHomologicalComplex (ComplexShape.up ℤ)

/-- Total tensor complexes, using precisely the recorded sheaf tensor and Koszul signs.
Source: Stacks, Section 06YL and Section 08J7
(blueprint: lem-sfb-derived-internal-hom-sections-model). -/
noncomputable def totalTensor :
    Complexes.{c, v, r} R ⥤ Complexes.{c, v, r} R ⥤ Complexes.{c, v, r} R :=
  letI := (SheafOfModules.isMonoidal_W_independentCoefficients R)
  letI := SheafOfModules.monoidalCategory R
  letI := (SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients R)
  letI := (SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients R)
  (curriedTensor (Modules.{c, v, r} R)).map₂HomologicalComplex
    (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)

set_option backward.isDefEq.respectTransparency true in
set_option synthInstance.maxSize 2048 in
set_option linter.unusedSectionVars false in
/-- Any right adjoint of the derived tensor functor is naturally the recorded internal Hom.
The hypothesis on T spells out the node's definition of derived tensor: for every K-flat
representative P of K, its value on any complex is the localized total tensor P tensor N.
It imposes no flatness or boundedness on the source representative used in the conclusions.

Source: Stacks, Section 08J7 (equation-internal-hom), Lemmas 08J9, 0A95 and 0A96
(blueprint: lem-sfb-derived-internal-hom-sections-model).

Proof: Use the recorded closed symmetric monoidal structure on the derived category.
Choose a K-flat resolution P of a complex representing K. Its localized augmentation
identifies Q(P) with K. The model hypothesis and the closed structure's natural
one-K-flat tensor comparison identify Q followed by T with Q followed by tensorLeft K.
Fully faithful precomposition with Q lifts this to T isomorphic to tensorLeft K.
Symmetry identifies tensorLeft K with tensorRight K. Transport the given adjunction
along this isomorphism, and apply uniqueness of right adjoints to the closed structure's
adjunction for the recorded internal Hom. -/
theorem tensorRightAdjoint_iso
    (K : Derived.{c, v, r, w} R) (T H : Derived.{c, v, r, w} R ⥤ Derived.{c, v, r, w} R)
    (model : ∀ (P : Complexes.{c, v, r} R),
      CochainComplex.IsKFlatIndependentCoefficients (R := R) P →
      (DerivedCategory.Q.obj P ≅ K) →
      Nonempty (DerivedCategory.Q ⋙ T ≅ (totalTensor.{c, v, r} R).obj P ⋙ DerivedCategory.Q))
    (adj : T ⊣ H) :
    Nonempty (H ≅ (internalHom.{c, v, r, w} R).obj (op K)) := by
  classical
  obtain ⟨S, M, β, ⟨h⟩⟩ := ringedDerived_closed_symmetric_monoidal.{c, v, r, w} J R
  let := S.monoidal
  let := β
  let L := DerivedCategory.Q.objPreimage K
  obtain ⟨P, p, hP, _, hp, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients L
  have : QuasiIso p := hp
  let e : DerivedCategory.Q.obj P ≅ K :=
    asIso (DerivedCategory.Q.map p) ≪≫ DerivedCategory.Q.objObjPreimageIso K
  obtain ⟨a⟩ := model P hP e
  let b : (totalTensor.{c, v, r} R).obj P ⋙ DerivedCategory.Q ≅
      DerivedCategory.Q ⋙ tensorLeft (DerivedCategory.Q.obj P) :=
    NatIso.ofComponents (fun N ↦ h.tensorIso P N (Or.inl hP)) (by
      intro N N' f
      have hn := h.tensorIso_naturality P N P N' (Or.inl hP) (Or.inl hP) (𝟙 P) f
      simpa only [WeilConjectures.coefficientTotalTensor, Functor.uncurry_obj_map,
        Functor.map_id, NatTrans.id_app, Category.id_comp, totalTensor, Functor.comp_map,
        WeilConjectures.CoefficientClosedStructure.tensor, tensorObj, tensorHom,
        MonoidalCategory.tensor_map, tensorHom_def, tensorLeft, id_whiskerRight,
        Category.id_comp, Modules, ringedSiteModules, curriedTensor] using hn)
  let d : tensorLeft (DerivedCategory.Q.obj P) ≅ tensorLeft K :=
    (curriedTensor (Derived.{c, v, r, w} R)).mapIso e
  let t : T ≅ tensorLeft K :=
    (Localization.fullyFaithfulWhiskeringLeft DerivedCategory.Q
      (HomologicalComplex.quasiIso (Modules.{c, v, r} R) (.up ℤ))
        (Derived.{c, v, r, w} R)).preimageIso
      (a ≪≫ b ≪≫ Functor.isoWhiskerLeft DerivedCategory.Q d)
  exact ⟨(adj.ofNatIsoLeft (t ≪≫ BraidedCategory.tensorLeftIsoTensorRight K)).rightAdjointUniq
    (S.adjunction K)⟩


attribute [local irreducible] derivedInternalHomOfUniverses homComplexFunctor

omit [HasDerivedCategory.{w} (Modules.{c, v, r} R)]
  [HasDerivedCategory.{z} AddCommGrpCat.{max c v r}] in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
-- Currying and its inverse involve the unbounded Hom-complex product and tensor instances.
private theorem homComplex_isKInjective
    (L I : Complexes.{c, v, r} R) (hL : L.IsKFlatIndependentCoefficients)
    [I.IsKInjective] : (homComplex (R := R) L I).IsKInjective := by
  classical
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients R
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients R
  refine ⟨fun {K} f hK ↦ ?_⟩
  let T := CochainComplex.mapBifunctor K L (curriedTensor _)
  obtain ⟨e, he⟩ := global_tensorHom_cochainsOfUniverses.{c, v, r} R K L I
  let z := CochainComplex.HomComplex.Cochain.ofHom f
  have hz : CochainComplex.HomComplex.δ 0 1 (e 0 z) = 0 := by
    rw [← he 0 1 (by omega), CochainComplex.HomComplex.δ_ofHom, map_zero]
  let c : CochainComplex.HomComplex.Cocycle T I 0 :=
    CochainComplex.HomComplex.Cocycle.mk _ 1 (by omega) hz
  obtain ⟨a, ha⟩ := CochainComplex.IsKInjective.eq_δ_of_cocycle c (hL K hK) (-1)
    (by omega)
  refine ⟨(CochainComplex.HomComplex.Cochain.equivHomotopy f 0).symm
    ⟨(e (-1)).symm a, ?_⟩⟩
  rw [CochainComplex.HomComplex.Cochain.ofHom_zero, add_zero]
  apply (e 0).injective
  rw [he (-1) 0 (by omega), AddEquiv.apply_symm_apply]
  exact ha.symm

omit [HasDerivedCategory.{z} AddCommGrpCat.{max c v r}] in
set_option backward.isDefEq.respectTransparency true in
private theorem representativeComparison :
    Nonempty (representedInternalHom.{c, v, r, w} R ≅
      representativeHom.{c, v, r} R ⋙ DerivedCategory.Q) := by
  let A := Modules.{c, v, r} R
  let : IsGrothendieckAbelian.{max c v r} A :=
    (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{c, v, r}
      J R).1
  let I := CochainComplex.kInjectiveResolutionFunctor.{max c v r} A
  let η := CochainComplex.toKInjectiveResolution.{max c v r} A
  let G := (𝟭 (Complexes.{c, v, r} R)ᵒᵖ).prod (injectiveProperty.{c, v, r} R).ι
  let H := Functor.uncurry.obj
    (homComplexFunctor.{c, v, max c v r, max c v r} (R := R)) ⋙ DerivedCategory.Q
  let α := Functor.whiskerLeft G
    (Functor.whiskerRight (NatTrans.prod (𝟙 (𝟭 _)) η) H)
  have : IsIso α := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro X
    have : X.2.obj.IsKInjective := X.2.property
    have : (I.obj X.2.obj).IsKInjective :=
      CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj.{max c v r} A _
    have : QuasiIso (η.app X.2.obj) :=
      (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{max c v r} A _).2
    change IsIso (DerivedCategory.Q.map
      (((homComplexFunctor.{c, v, max c v r, max c v r} (R := R)).map (𝟙 X.1.unop).op).app X.2.obj ≫
        ((homComplexFunctor.{c, v, max c v r, max c v r}
          (R := R)).obj (op X.1.unop)).map (η.app X.2.obj)))
    apply (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mpr
    exact quasiIso_homComplex_mapOfUniverses.{c, v, r}
      (I' := X.2.obj) (I := I.obj X.2.obj) (η.app X.2.obj) (𝟙 X.1.unop)
  obtain ⟨e⟩ := derivedInternalHomOfUniverses_comparison.{c, v, r, w} J R I η (fun M ↦
    ⟨(CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{max c v r} A M).2,
      CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj.{max c v r} A M⟩)
  exact ⟨Functor.isoWhiskerLeft G e ≪≫ (asIso α).symm⟩

set_option backward.isDefEq.respectTransparency false in
private theorem sectionsComparison :
    Nonempty ((representativeHom.{c, v, r} R ⋙ DerivedCategory.Q) ⋙
        derivedSections.{c, v, r, w, z} R ≅ globalHom.{c, v, r} R ⋙ DerivedCategory.Q) := by
  classical
  let A := Modules.{c, v, r} R
  let : IsGrothendieckAbelian.{max c v r} A :=
    (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{c, v, r}
      J R).1
  let Γ := sections.{c, v, r} R
  let q := HomotopyCategory.quotient A (.up ℤ)
  let G := Γ.mapHomologicalComplex (.up ℤ)
  let e : q ⋙ Γ.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh ≅
      G ⋙ DerivedCategory.Q :=
    Functor.isoWhiskerRight (Γ.mapHomotopyCategoryFactors (.up ℤ)) DerivedCategory.Qh ≪≫
      Functor.isoWhiskerLeft G (DerivedCategory.quotientCompQhIso AddCommGrpCat.{max c v r})
  let α : G ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ Γ.rightDerivedFunctor :=
    e.inv ≫ Functor.whiskerLeft q Γ.rightDerivedFunctorUnit ≫
      (Functor.isoWhiskerRight (DerivedCategory.quotientCompQhIso A)
        Γ.rightDerivedFunctor).hom
  have hα (T : CochainComplex A ℤ) [T.IsKInjective] : IsIso (α.app T) := by
    dsimp [α]
    infer_instance
  let F := representativeHom.{c, v, r} R
  let γ := Functor.whiskerLeft F α
  have hγ : ∀ X, IsIso (γ.app X) := by
    rintro ⟨L, I⟩
    obtain ⟨P, t, hP, _, ht, _⟩ :=
      CochainComplex.exists_isKFlatResolutionIndependentCoefficients L.unop
    let := ht
    let : I.obj.IsKInjective := I.property
    let f : (L, I) ⟶ (op P, I) := (t.op, 𝟙 I)
    have hf : QuasiIso (F.map f) := by
      change QuasiIso
        (((homComplexFunctor.{c, v, max c v r, max c v r} (R := R)).map t.op).app I.obj ≫
          ((homComplexFunctor.{c, v, max c v r, max c v r} (R := R)).obj (op P)).map (𝟙 I.obj))
      exact quasiIso_homComplex_mapOfUniverses.{c, v, r} (𝟙 I.obj) t
    let := hf
    have hright : IsIso ((F ⋙ DerivedCategory.Q ⋙ Γ.rightDerivedFunctor).map f) := by
      change IsIso (Γ.rightDerivedFunctor.map (DerivedCategory.Q.map (F.map f)))
      infer_instance
    have hleft : IsIso ((F ⋙ G ⋙ DerivedCategory.Q).map f) := by
      have hq : QuasiIso (G.map (F.map f)) := by
        let m := G.map (F.map f)
        have he : m ≫ (CategoryTheory.globalComplexIso.{c, v, r} R (op P, I.obj)).hom =
            (CategoryTheory.globalComplexIso.{c, v, r} R (L, I.obj)).hom ≫
              CategoryTheory.externalMap t (𝟙 I.obj) :=
          CategoryTheory.globalComplexIso_naturality.{c, v, r} R t (𝟙 I.obj)
        let := GlobalCochains.externalMap_quasiIso t (I := I.obj)
        have : QuasiIso (m ≫ (CategoryTheory.globalComplexIso.{c, v, r}
            R (op P, I.obj)).hom) := by
          rw [he]
          infer_instance
        exact quasiIso_of_comp_right m
          (CategoryTheory.globalComplexIso.{c, v, r} R (op P, I.obj)).hom
      let := hq
      change IsIso (DerivedCategory.Q.map (G.map (F.map f)))
      infer_instance
    let := hleft
    let := hright
    have hflat : (F.obj (op P, I)).IsKInjective := by
      change (homComplex (R := R) P I.obj).IsKInjective
      exact homComplex_isKInjective.{c, v, r} R P I.obj hP
    let := hflat
    have : IsIso (γ.app (op P, I)) := hα _
    have hn := γ.naturality f
    have : IsIso (γ.app (L, I) ≫
        (F ⋙ DerivedCategory.Q ⋙ Γ.rightDerivedFunctor).map f) := by
      rw [← hn]
      infer_instance
    exact IsIso.of_isIso_comp_right (γ.app (L, I))
      ((F ⋙ DerivedCategory.Q ⋙ Γ.rightDerivedFunctor).map f)
  let : IsIso γ := (NatTrans.isIso_iff_isIso_app γ).mpr hγ
  exact ⟨(asIso γ).symm⟩

/-- Natural K-injective models for the internal Hom, its full derived global sections,
and all of its hypercohomology groups. The third comparison identifies the ordinary
sections complex with the usual global Hom complex, including its differential and
its degree-n product of morphism groups.

Source: Stacks, Section 08J7, Lemmas 08JA, 08J9, 0A95 and 0A96
(blueprint: lem-sfb-derived-internal-hom-sections-model).

Proof: First compare the canonical functorial K-injective replacement of I with I
itself. Its resolution map is a quasi-isomorphism between K-injectives. Applying
Hom(A,-) and Q inverts it by 0A95. The resulting comparison with the localized
internal Hom is natural in every source chain map and every map between K-injectives.
Next replace A by a K-flat P. Hom(P,I) is K-injective by 0A96, hence RΓ is computed
by ordinary sections on it. A quasi-isomorphism P to A induces quasi-isomorphisms
on both sheaf Hom complexes and global Hom complexes, since I is K-injective.
This transports the full-complex comparison back to A. Functorial resolutions and
naturality of pre- and postcomposition give the displayed natural isomorphism.
In each degree, sections commute with products and sections of sheaf Hom are global
module maps. These identifications give the third chain isomorphism: its differential
is d_I f - (-1)^n f d_A. The same component formula gives the naturality equation below.
Finally the cohomology of the global Hom complex is homotopy classes A to I[n].
K-injectivity identifies these with derived morphisms. Transport along representatives
of K and M gives the last assertion for every integer n, including negative n.
Zero complexes and the empty site are included; no boundedness or flatness of A is used. -/
theorem derived_internalHom_sections_model :
    Nonempty (representedInternalHom.{c, v, r, w} R ≅
      representativeHom.{c, v, r} R ⋙ DerivedCategory.Q) ∧
    Nonempty (representedInternalHom.{c, v, r, w} R ⋙ derivedSections.{c, v, r, w, z} R ≅
      globalHom.{c, v, r} R ⋙ DerivedCategory.Q) ∧
    (∃ e : ∀ (A I : Complexes.{c, v, r} R),
        ((sections.{c, v, r} R).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (homComplex (R := R) A I) ≅ CochainComplex.HomComplex A I,
      ∀ (A A' I I' : Complexes.{c, v, r} R) (f : A' ⟶ A) (g : I ⟶ I')
        (n p q : ℤ) (hpq : p + n = q)
        (s : (((sections.{c, v, r} R).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (homComplex (R := R) A I)).X n),
        ((e A' I').hom.f n
          ((((sections.{c, v, r} R).mapHomologicalComplex (ComplexShape.up ℤ)).map
            (((homComplexFunctor (R := R)).map f.op).app I ≫
              ((homComplexFunctor (R := R)).obj (op A')).map g)).f n s)).v p q hpq =
          f.f p ≫ ((e A I).hom.f n s).v p q hpq ≫ g.f q) ∧
    (∀ (K M : Derived.{c, v, r, w} R) (n : ℤ),
      Nonempty (((DerivedCategory.homologyFunctor.{z} AddCommGrpCat.{max c v r} n).obj
        ((derivedSections.{c, v, r, w, z} R).obj
          (((internalHom.{c, v, r, w} R).obj (op K)).obj M))) ≃+
          (K ⟶ M⟦n⟧))) := by
  classical
  obtain ⟨a⟩ := representativeComparison.{c, v, r, w} R
  obtain ⟨s⟩ := sectionsComparison.{c, v, r, w, z} R
  let e := Functor.isoWhiskerRight a (derivedSections.{c, v, r, w, z} R) ≪≫ s
  refine ⟨⟨a⟩, ⟨e⟩, ?_, ?_⟩
  · refine ⟨fun A I ↦ CategoryTheory.globalComplexIso.{c, v, r} R (op A, I), ?_⟩
    intro A A' I I' f g n p q hpq s
    have h := CategoryTheory.globalComplexIso_naturality.{c, v, r} R f g
    have h' := ConcreteCategory.congr_hom (congrArg (fun k ↦ k.f n) h) s
    exact (congrArg (fun a ↦ a.v p q hpq) h').trans
      (CategoryTheory.externalMap_v f g n _ p q hpq)
  · intro K M n
    let B := Modules.{c, v, r} R
    let : IsGrothendieckAbelian.{max c v r} B :=
      (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{c, v, r}
        J R).1
    let A := DerivedCategory.Q.objPreimage K
    let eA : DerivedCategory.Q.obj A ≅ K := DerivedCategory.Q.objObjPreimageIso K
    obtain ⟨I, hI, ⟨eI⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isKInjective M
    let := hI
    let X : (Complexes.{c, v, r} R)ᵒᵖ × (injectiveProperty.{c, v, r} R).FullSubcategory :=
      (op A, ⟨I, hI⟩)
    let h : ((internalHom.{c, v, r, w} R).obj (op K)).obj M ≅
        (representedInternalHom.{c, v, r, w} R).obj X :=
      ((internalHom.{c, v, r, w} R).mapIso eA.op).app M ≪≫
        ((internalHom.{c, v, r, w} R).obj (op (DerivedCategory.Q.obj A))).mapIso eI
    let Hd := DerivedCategory.homologyFunctor.{z} AddCommGrpCat.{max c v r} n
    let H := HomologicalComplex.homologyFunctor AddCommGrpCat.{max c v r} (.up ℤ) n
    let d : Hd.obj ((derivedSections.{c, v, r, w, z} R).obj
          (((internalHom.{c, v, r, w} R).obj (op K)).obj M)) ≅
        H.obj (CochainComplex.HomComplex A I) :=
      Hd.mapIso ((derivedSections.{c, v, r, w, z} R).mapIso h ≪≫ e.app X) ≪≫
        (DerivedCategory.homologyFunctorFactors.{z} AddCommGrpCat.{max c v r} n).app _ ≪≫
          H.mapIso (CategoryTheory.globalComplexIso.{c, v, r} R (op A, I))
    let q := HomotopyCategory.quotient B (.up ℤ)
    let σ := DerivedCategory.quotientCompQhIso.{w} B
    let b : (DerivedCategory.Qh.obj (q.obj A) ⟶
          DerivedCategory.Qh.obj (q.obj (I⟦n⟧))) ≃+
        (DerivedCategory.Q.obj A ⟶ (DerivedCategory.Q.obj I)⟦n⟧) :=
      { toEquiv := Iso.homCongr (σ.app A)
          (σ.app (I⟦n⟧) ≪≫ (DerivedCategory.Q.commShiftIso n).app I)
        map_add' := by intros; simp [Preadditive.comp_add, Preadditive.add_comp] }
    let t : (DerivedCategory.Q.obj A ⟶ (DerivedCategory.Q.obj I)⟦n⟧) ≃+
        (K ⟶ M⟦n⟧) :=
      { toEquiv := Iso.homCongr eA ((shiftFunctor _ n).mapIso eI.symm)
        map_add' := by intros; simp [Preadditive.comp_add, Preadditive.add_comp] }
    exact ⟨(Iso.addCommGroupIsoToAddEquiv d).trans
      ((Iso.addCommGroupIsoToAddEquiv (GlobalCochains.externalHomologyIsoDegree A I n)).trans
        ((AddEquiv.ofBijective DerivedCategory.Qh.mapAddHom
          (CochainComplex.IsKInjective.Qh_map_bijective (q.obj A) (I⟦n⟧))).trans
            (b.trans t)))⟩

end CategoryTheory.DerivedInternalHomSectionsModel
