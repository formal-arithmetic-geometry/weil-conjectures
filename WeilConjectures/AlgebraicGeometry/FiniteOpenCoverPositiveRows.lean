/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteOpenCoverRowComparison
import WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.Exact
import WeilConjectures.CategoryTheory.Sites.Categorical.CategoricalInjectiveCechExactness
import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts
import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
import WeilConjectures.AlgebraicGeometry.AlternatingCechComputes

/-! # Exact ordered relative Čech rows of injective étale module sheaves

Source: Stacks Project, Tag 03AZ, row calculation; Tags 03FB and 03FC for
injective module presheaves, and Tags 01FJ–01FM for the ordered comparison.
(blueprint: new-finite-cover-positive-rows-exact)
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

variable {X Y : Scheme.{u}} (B : Type (u + 1)) [CommRing B]

private def finiteCoverTestOverFunctor (f : X ⟶ Y) (T : Y.Etale) :
    X.Opens ⥤ Over ((finiteCoverTestObjectFunctor f T).obj ⊤) where
  obj V := Over.mk ((finiteCoverTestObjectFunctor f T).map (homOfLE (le_top : V ≤ ⊤)))
  map {V W} h := Over.homMk ((finiteCoverTestObjectFunctor f T).map h) (by
    change (finiteCoverTestObjectFunctor f T).map h ≫
      (finiteCoverTestObjectFunctor f T).map (homOfLE le_top) =
        (finiteCoverTestObjectFunctor f T).map (homOfLE le_top)
    rw [← Functor.map_comp]
    congr 1)
  map_id V := by
    apply Over.OverMorphism.ext
    exact (finiteCoverTestObjectFunctor f T).map_id V
  map_comp h k := by
    apply Over.OverMorphism.ext
    exact (finiteCoverTestObjectFunctor f T).map_comp h k

private def finiteCoverTestOverBinaryIsLimit (f : X ⟶ Y) (T : Y.Etale)
    (V W : X.Opens) :
    IsLimit (BinaryFan.mk
      ((finiteCoverTestOverFunctor f T).map (homOfLE (inf_le_left : V ⊓ W ≤ V)))
      ((finiteCoverTestOverFunctor f T).map (homOfLE (inf_le_right : V ⊓ W ≤ W)))) := by
  let P := finiteCoverTestObject_inf_isPullback f T V W
  refine BinaryFan.isLimitMk (fun s ↦ Over.homMk
    (P.lift s.fst.left s.snd.left (s.fst.w.trans s.snd.w.symm)) ?_) ?_ ?_ ?_
  · change P.lift _ _ _ ≫ finiteCoverTestObjectHom f T le_top = s.pt.hom
    calc
      _ = P.lift _ _ _ ≫
          (finiteCoverTestObjectHom f T (inf_le_left : V ⊓ W ≤ V) ≫
            finiteCoverTestObjectHom f T (le_top : V ≤ ⊤)) := by
        congr 1
        exact (finiteCoverTestObjectFunctor f T).map_comp
          (homOfLE inf_le_left) (homOfLE le_top)
      _ = s.fst.left ≫ finiteCoverTestObjectHom f T le_top := by
        rw [← Category.assoc, P.lift_fst]
      _ = _ := s.fst.w
  · intro s
    apply Over.OverMorphism.ext
    exact P.lift_fst _ _ _
  · intro s
    apply Over.OverMorphism.ext
    exact P.lift_snd _ _ _
  · intro s a ha hb
    apply Over.OverMorphism.ext
    apply P.hom_ext
    · exact (congrArg (fun z ↦ z.left) ha).trans (P.lift_fst _ _ _).symm
    · exact (congrArg (fun z ↦ z.left) hb).trans (P.lift_snd _ _ _).symm

private theorem finiteCoverTestOver_preservesPair (f : X ⟶ Y) (T : Y.Etale)
    (V W : X.Opens) :
    PreservesLimit (pair V W) (finiteCoverTestOverFunctor f T) := by
  let c := BinaryFan.mk (homOfLE (inf_le_left : V ⊓ W ≤ V))
    (homOfLE (inf_le_right : V ⊓ W ≤ W))
  have hc : IsLimit c := BinaryFan.isLimitMk
    (fun s ↦ homOfLE (le_inf (leOfHom s.fst) (leOfHom s.snd)))
    (fun _ ↦ Subsingleton.elim _ _) (fun _ ↦ Subsingleton.elim _ _)
    (fun _ _ _ _ ↦ Subsingleton.elim _ _)
  exact preservesLimit_of_preserves_limit_cone hc
    ((isLimitMapConeBinaryFanEquiv (finiteCoverTestOverFunctor f T) _ _).symm
      (finiteCoverTestOverBinaryIsLimit f T V W))

private instance finiteCoverTestOver_preservesBinary (f : X ⟶ Y) (T : Y.Etale) :
    PreservesLimitsOfShape (Discrete WalkingPair) (finiteCoverTestOverFunctor f T) where
  preservesLimit := by
    intro K
    haveI := finiteCoverTestOver_preservesPair f T
      (K.obj ⟨WalkingPair.left⟩) (K.obj ⟨WalkingPair.right⟩)
    exact preservesLimit_of_iso_diagram (finiteCoverTestOverFunctor f T) (diagramIsoPair K).symm

private instance finiteCoverTestOver_preservesTerminal (f : X ⟶ Y) (T : Y.Etale) :
    PreservesLimitsOfShape (Discrete PEmpty.{1}) (finiteCoverTestOverFunctor f T) := by
  let e : (finiteCoverTestOverFunctor f T).obj ⊤ ≅
      Over.mk (𝟙 (finiteCoverTestObject f T ⊤)) := Over.isoMk (Iso.refl _) (by
    change 𝟙 _ = (finiteCoverTestObjectFunctor f T).map (homOfLE (le_top : ⊤ ≤ ⊤))
    simpa only [homOfLE_refl] using ((finiteCoverTestObjectFunctor f T).map_id ⊤).symm)
  have ht : IsTerminal ((finiteCoverTestOverFunctor f T).obj ⊤) :=
    Over.mkIdTerminal.ofIso e.symm
  haveI : PreservesLimit (Functor.empty X.Opens) (finiteCoverTestOverFunctor f T) :=
    preservesLimit_of_preserves_limit_cone isTerminalTop
      ((isLimitMapConeEmptyConeEquiv (finiteCoverTestOverFunctor f T) ⊤).symm ht)
  exact preservesLimitsOfShape_pempty_of_preservesTerminal (finiteCoverTestOverFunctor f T)

private instance finiteCoverTestOver_preservesFiniteProducts (f : X ⟶ Y) (T : Y.Etale) :
    PreservesFiniteProducts (finiteCoverTestOverFunctor f T) :=
  PreservesFiniteProducts.of_preserves_binary_and_terminal _

attribute [local instance] Over.ConstructProducts.over_finiteProducts_of_finiteWidePullbacks

private def finiteCoverTestTupleIso (f : X ⟶ Y) (T : Y.Etale) {m : ℕ}
    (U : Fin m → X.Opens) (p : ℕ) (t : Fin (p + 1) → Fin m) :
    (finiteCoverTestOverFunctor f T).obj (⨅ k, U (t k)) ≅
      ∏ᶜ (fun k ↦ (finiteCoverTestOverFunctor f T).obj (U (t k))) :=
  (isLimitFanMkObjOfIsLimit (finiteCoverTestOverFunctor f T) (fun k ↦ U (t k))
    (fun k ↦ homOfLE (iInf_le (fun k ↦ U (t k)) k))
    (Preorder.isLimitIInf (fun k ↦ U (t k)))).conePointUniqueUpToIso (limit.isLimit _)

private theorem finiteCoverTestTupleIso_hom_π (f : X ⟶ Y) (T : Y.Etale) {m : ℕ}
    (U : Fin m → X.Opens) (p : ℕ) (t : Fin (p + 1) → Fin m) (k : Fin (p + 1)) :
    (finiteCoverTestTupleIso f T U p t).hom ≫
        Pi.π (fun k ↦ (finiteCoverTestOverFunctor f T).obj (U (t k))) k =
      (finiteCoverTestOverFunctor f T).map
        (homOfLE (iInf_le (fun k ↦ U (t k)) k)) :=
  IsLimit.conePointUniqueUpToIso_hom_comp _ _ (Discrete.mk k)

private theorem finiteCoverTestTupleIso_indexMap (f : X ⟶ Y) (T : Y.Etale) {m : ℕ}
    (U : Fin m → X.Opens) {p q : ℕ} (t : Fin (p + 1) → Fin m)
    (α : Fin (q + 1) → Fin (p + 1)) :
    (finiteCoverTestTupleIso f T U p t).hom ≫
        Pi.lift (fun k ↦ Pi.π
          (fun l ↦ (finiteCoverTestOverFunctor f T).obj (U (t l))) (α k)) =
      (finiteCoverTestOverFunctor f T).map
          (homOfLE (le_iInf fun k ↦ iInf_le (fun l ↦ U (t l)) (α k))) ≫
        (finiteCoverTestTupleIso f T U q (t ∘ α)).hom := by
  apply Pi.hom_ext
  intro k
  rw [Category.assoc, Pi.lift_π, finiteCoverTestTupleIso_hom_π]
  have h := congrArg (fun z ↦
    (finiteCoverTestOverFunctor f T).map
      (homOfLE (le_iInf fun k ↦ iInf_le (fun l ↦ U (t l)) (α k))) ≫ z)
    (finiteCoverTestTupleIso_hom_π f T U q (t ∘ α) k)
  exact h.trans ((finiteCoverTestOverFunctor f T).map_comp _ _).symm |>.symm

private def finiteCoverModulePiIso {I : Type} (A : I → ModuleCat.{u + 1} B) :
    (∏ᶜ A) ≅ ModuleCat.of B (∀ i, A i) :=
  ((ModuleCat.HasLimit.productLimitCone A).isLimit.conePointUniqueUpToIso
    (limit.isLimit _)).symm

private theorem finiteCoverModulePiIso_hom_eval {I : Type}
    (A : I → ModuleCat.{u + 1} B) (i : I) :
    (finiteCoverModulePiIso B A).hom ≫
        ModuleCat.ofHom (LinearMap.proj i : (∀ i, A i) →ₗ[B] A i) = Pi.π A i :=
  IsLimit.conePointUniqueUpToIso_inv_comp
    (ModuleCat.HasLimit.productLimitCone A).isLimit (limit.isLimit _) (Discrete.mk i)

private abbrev finiteCoverFullTestComplex (f : X ⟶ Y) (T : Y.Etale)
    {m : ℕ} (U : Fin m → X.Opens)
    (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)) :
    CochainComplex (ModuleCat.{u + 1} B) ℕ :=
  (cechComplexFunctor (fun i ↦ (finiteCoverTestOverFunctor f T).obj (U i))).obj
    ((Over.forget ((finiteCoverTestObjectFunctor f T).obj ⊤)).op ⋙ M.obj)

private def finiteCoverFullTestDegreeIso (f : X ⟶ Y) (T : Y.Etale)
    {m : ℕ} (U : Fin m → X.Opens)
    (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)) (p : ℕ) :
    (finiteCoverFullTestComplex B f T U M).X p ≅
      ModuleCat.of B (∀ t : Fin (p + 1) → Fin m,
        (finiteCoverSectionPresheaf B f T M).obj (op (⨅ k, U (t k)))) :=
  Pi.mapIso (fun t ↦ M.obj.mapIso
    (((Over.forget ((finiteCoverTestObjectFunctor f T).obj ⊤)).mapIso
      (finiteCoverTestTupleIso f T U p t)).op)) ≪≫ finiteCoverModulePiIso B _

private theorem finiteCoverFullTestDegreeIso_hom_eval (f : X ⟶ Y) (T : Y.Etale)
    {m : ℕ} (U : Fin m → X.Opens)
    (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)) (p : ℕ)
    (t : Fin (p + 1) → Fin m) :
    (finiteCoverFullTestDegreeIso B f T U M p).hom ≫ ModuleCat.ofHom
        (LinearMap.proj t : (∀ t : Fin (p + 1) → Fin m,
          (finiteCoverSectionPresheaf B f T M).obj (op (⨅ k, U (t k)))) →ₗ[B]
            (finiteCoverSectionPresheaf B f T M).obj (op (⨅ k, U (t k)))) =
      Pi.π (fun t : Fin (p + 1) → Fin m ↦ M.obj.obj (op
        (∏ᶜ (fun k ↦ (finiteCoverTestOverFunctor f T).obj (U (t k)))).left)) t ≫
          M.obj.map ((finiteCoverTestTupleIso f T U p t).hom.left).op := by
  simp only [finiteCoverFullTestDegreeIso, Iso.trans_hom, Category.assoc,
    finiteCoverModulePiIso_hom_eval, Pi.mapIso_hom_π, Functor.mapIso_hom]
  rfl

private theorem finiteCoverFullTestComplex_d_π (f : X ⟶ Y) (T : Y.Etale)
    {m : ℕ} (U : Fin m → X.Opens)
    (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)) (p : ℕ)
    (t : Fin (p + 2) → Fin m) :
    (finiteCoverFullTestComplex B f T U M).d p (p + 1) ≫
        Pi.π (fun t : Fin (p + 2) → Fin m ↦ M.obj.obj (op
          (∏ᶜ (fun k ↦ (finiteCoverTestOverFunctor f T).obj (U (t k)))).left)) t =
      ∑ j : Fin (p + 2), (-1 : ℤ) ^ (j : ℕ) •
        (Pi.π (fun s : Fin (p + 1) → Fin m ↦ M.obj.obj (op
            (∏ᶜ (fun k ↦ (finiteCoverTestOverFunctor f T).obj (U (s k)))).left))
            (t ∘ j.succAbove) ≫
          M.obj.map ((Pi.lift (fun k ↦ Pi.π
            (fun l ↦ (finiteCoverTestOverFunctor f T).obj (U (t l)))
            (j.succAbove k))).left).op) := by
  rw [cechComplexFunctor_obj_d]
  simp only [Preadditive.sum_comp, Preadditive.zsmul_comp]
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  change (Pi.lift (fun s : Fin (p + 2) → Fin m ↦
    Pi.π (fun s : Fin (p + 1) → Fin m ↦ M.obj.obj (op
      (∏ᶜ (fun k ↦ (finiteCoverTestOverFunctor f T).obj (U (s k)))).left))
      (s ∘ j.succAbove) ≫ M.obj.map ((Pi.lift (fun k ↦ Pi.π
        (fun l ↦ (finiteCoverTestOverFunctor f T).obj (U (s l)))
        (j.succAbove k))).left).op)) ≫ Pi.π _ t = _
  exact Pi.lift_π _ t

private theorem finiteCoverFullTestDegreeIso_d_eval (f : X ⟶ Y) (T : Y.Etale)
    {m : ℕ} (U : Fin m → X.Opens)
    (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)) (p : ℕ)
    (t : Fin (p + 2) → Fin m) :
    (finiteCoverFullTestComplex B f T U M).d p (p + 1) ≫
        (finiteCoverFullTestDegreeIso B f T U M (p + 1)).hom ≫ ModuleCat.ofHom
          (LinearMap.proj t : (∀ t : Fin (p + 2) → Fin m,
            (finiteCoverSectionPresheaf B f T M).obj (op (⨅ k, U (t k)))) →ₗ[B]
              (finiteCoverSectionPresheaf B f T M).obj (op (⨅ k, U (t k)))) =
      ∑ j : Fin (p + 2), (-1 : ℤ) ^ (j : ℕ) •
        ((finiteCoverFullTestDegreeIso B f T U M p).hom ≫ ModuleCat.ofHom
          (LinearMap.proj (t ∘ j.succAbove) : (∀ s : Fin (p + 1) → Fin m,
            (finiteCoverSectionPresheaf B f T M).obj (op (⨅ k, U (s k)))) →ₗ[B]
              (finiteCoverSectionPresheaf B f T M).obj
                (op (⨅ k, U ((t ∘ j.succAbove) k)))) ≫
          (finiteCoverSectionPresheaf B f T M).map
            (homOfLE (le_iInf fun k ↦
              iInf_le (fun l ↦ U (t l)) (j.succAbove k))).op) := by
  rw [finiteCoverFullTestDegreeIso_hom_eval, ← Category.assoc,
    finiteCoverFullTestComplex_d_π]
  simp only [Preadditive.sum_comp, Preadditive.zsmul_comp, Category.assoc]
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  have h := finiteCoverFullTestDegreeIso_hom_eval B f T U M p (t ∘ j.succAbove)
  have hc : M.obj.map
        ((Pi.lift (fun k ↦ Pi.π
          (fun l ↦ (finiteCoverTestOverFunctor f T).obj (U (t l)))
          (j.succAbove k))).left).op ≫
        M.obj.map ((finiteCoverTestTupleIso f T U (p + 1) t).hom.left).op =
      M.obj.map ((finiteCoverTestTupleIso f T U p (t ∘ j.succAbove)).hom.left).op ≫
        (finiteCoverSectionPresheaf B f T M).map
          (homOfLE (le_iInf fun k ↦
            iInf_le (fun l ↦ U (t l)) (j.succAbove k))).op := by
    simp only [finiteCoverSectionPresheaf, Functor.comp_map, Functor.op_map]
    rw [← M.obj.map_comp, ← M.obj.map_comp, ← op_comp, ← op_comp]
    exact congrArg (fun z ↦ M.obj.map z.op)
      (congrArg (fun z ↦ z.left) (finiteCoverTestTupleIso_indexMap f T U t j.succAbove))
  let pr : (finiteCoverFullTestComplex B f T U M).X p ⟶
      M.obj.obj (op (∏ᶜ (fun k ↦
        (finiteCoverTestOverFunctor f T).obj (U ((t ∘ j.succAbove) k)))).left) :=
    Pi.π (fun s : Fin (p + 1) → Fin m ↦ M.obj.obj (op
      (∏ᶜ (fun k ↦ (finiteCoverTestOverFunctor f T).obj (U (s k)))).left))
      (t ∘ j.succAbove)
  have hh := congrArg (fun z ↦ pr ≫ z) hc
  have hh' := congrArg (fun z ↦ z ≫
    (finiteCoverSectionPresheaf B f T M).map
      (homOfLE (le_iInf fun k ↦
        iInf_le (fun l ↦ U (t l)) (j.succAbove k))).op) h
  exact hh.trans ((Category.assoc _ _ _).symm.trans hh'.symm) |>.trans
    (Category.assoc _ _ _)

private def finiteCoverOpenCech {m : ℕ} (U : Fin m → X.Opens) :
    SiteCechComplex U (fun i ↦ homOfLE (le_top : U i ≤ ⊤)) where
  W p t := ⨅ k : Fin (p + 1), U (t k)
  pr p t k := homOfLE (iInf_le (fun k ↦ U (t k)) k)
  comm _ _ _ := Subsingleton.elim _ _
  universal p t Z a _ := by
    refine ⟨homOfLE (le_iInf (fun k ↦ leOfHom (a k))), ?_, ?_⟩
    · intro k
      exact Subsingleton.elim _ _
    · intro b _
      exact Subsingleton.elim _ _
  W_zero t := by simp
  pr_zero _ := Subsingleton.elim _ _
  indexMap t α := homOfLE (le_iInf fun k ↦ iInf_le (fun l ↦ U (t l)) (α k))
  indexMap_pr _ _ _ := Subsingleton.elim _ _

private def finiteCoverFullTestAbDegreeIso (f : X ⟶ Y) (T : Y.Etale)
    {m : ℕ} (U : Fin m → X.Opens)
    (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)) (p : ℕ) :
    (forget₂ (ModuleCat.{u + 1} B) AddCommGrpCat).obj
        ((finiteCoverFullTestComplex B f T U M).X p) ≅
      (finiteCoverOpenCech U).cochains
        (finiteCoverSectionPresheaf B f T M ⋙ forget₂ (ModuleCat B) AddCommGrpCat) p :=
  (forget₂ (ModuleCat.{u + 1} B) AddCommGrpCat).mapIso
    (finiteCoverFullTestDegreeIso B f T U M p)

private theorem finiteCoverFullTestAbDegreeIso_comm (f : X ⟶ Y) (T : Y.Etale)
    {m : ℕ} (U : Fin m → X.Opens)
    (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)) (p : ℕ) :
    (finiteCoverFullTestAbDegreeIso B f T U M p).hom ≫
        ((finiteCoverOpenCech U).complex
          (finiteCoverSectionPresheaf B f T M ⋙
            forget₂ (ModuleCat B) AddCommGrpCat)).d p (p + 1) =
      (forget₂ (ModuleCat B) AddCommGrpCat).map
          ((finiteCoverFullTestComplex B f T U M).d p (p + 1)) ≫
        (finiteCoverFullTestAbDegreeIso B f T U M (p + 1)).hom := by
  apply AddCommGrpCat.ext
  intro x
  change (finiteCoverFullTestComplex B f T U M).X p at x
  funext t
  have h := ConcreteCategory.congr_hom
    (finiteCoverFullTestDegreeIso_d_eval B f T U M p t) x
  change (finiteCoverFullTestDegreeIso B f T U M (p + 1)).hom
      ((finiteCoverFullTestComplex B f T U M).d p (p + 1) x) t =
    (∑ j : Fin (p + 2), (-1 : ℤ) ^ (j : ℕ) •
      ((finiteCoverFullTestDegreeIso B f T U M p).hom ≫ ModuleCat.ofHom
        (LinearMap.proj (t ∘ j.succAbove) : (∀ s : Fin (p + 1) → Fin m,
          (finiteCoverSectionPresheaf B f T M).obj (op (⨅ k, U (s k)))) →ₗ[B]
            (finiteCoverSectionPresheaf B f T M).obj
              (op (⨅ k, U ((t ∘ j.succAbove) k)))) ≫
        (finiteCoverSectionPresheaf B f T M).map
          (homOfLE (le_iInf fun k ↦
            iInf_le (fun l ↦ U (t l)) (j.succAbove k))).op)).hom x at h
  symm
  simp only [finiteCoverFullTestAbDegreeIso, Functor.mapIso_hom,
    SiteCechComplex.complex, CochainComplex.of_d,
    SiteCechComplex.differential, SiteCechComplex.differentialValue,
    AddCommGrpCat.comp_apply, ModuleCat.forget₂_map, AddCommGrpCat.ofHom_apply]
  change (finiteCoverFullTestDegreeIso B f T U M (p + 1)).hom
      ((finiteCoverFullTestComplex B f T U M).d p (p + 1) x) t =
    ∑ j : Fin (p + 2), (-1 : ℤ) ^ (j : ℕ) •
      (finiteCoverSectionPresheaf B f T M).map
        (homOfLE (le_iInf fun k ↦
          iInf_le (fun l ↦ U (t l)) (j.succAbove k))).op
        ((finiteCoverFullTestDegreeIso B f T U M p).hom x (t ∘ j.succAbove))
  simpa only [ModuleCat.hom_sum, ModuleCat.hom_zsmul, ModuleCat.hom_comp,
    ModuleCat.hom_ofHom, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.comp_apply, LinearMap.proj_apply] using! h

private def finiteCoverFullTestAbIso (f : X ⟶ Y) (T : Y.Etale)
    {m : ℕ} (U : Fin m → X.Opens)
    (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)) :
    ((forget₂ (ModuleCat B) AddCommGrpCat).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (finiteCoverFullTestComplex B f T U M) ≅
      (finiteCoverOpenCech U).complex
        (finiteCoverSectionPresheaf B f T M ⋙ forget₂ (ModuleCat B) AddCommGrpCat) :=
  HomologicalComplex.Hom.isoOfComponents (finiteCoverFullTestAbDegreeIso B f T U M)
    (by
      rintro p q (rfl : p + 1 = q)
      exact finiteCoverFullTestAbDegreeIso_comm B f T U M p)

private def finiteCoverOrderedCoordinates (f : X ⟶ Y) (T : Y.Etale)
    {m : ℕ} (U : Fin m → X.Opens)
    (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)) (p : ℕ) :
    (forget₂ (ModuleCat B) AddCommGrpCat).obj (finiteCoverSectionTerm B f T M U p) ≅
      AddCommGrpCat.of (∀ t : {t : Fin (p + 1) → Fin m // StrictMono t},
        (finiteCoverSectionPresheaf B f T M).obj (op (⨅ k, U (t.1 k)))) :=
  AddEquiv.toAddCommGrpIso
    ((ModuleCat.biproductIsoPi (fun a : Fin (p + 1) ↪o Fin m ↦
      (finiteCoverSectionPresheaf B f T M).obj (op (⨅ k, U (a k))))).toLinearEquiv.toAddEquiv.trans
      { toFun := fun s t ↦ s (OrderEmbedding.ofStrictMono t.1 t.2)
        invFun := fun s a ↦ s ⟨a, a.strictMono⟩
        left_inv := fun _ ↦ by funext a; rfl
        right_inv := fun _ ↦ by funext t; rfl
        map_add' := fun _ _ ↦ rfl })

private theorem finiteCoverOrderedCoordinates_apply (f : X ⟶ Y) (T : Y.Etale)
    {m : ℕ} (U : Fin m → X.Opens)
    (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)) (p : ℕ)
    (x : finiteCoverSectionTerm B f T M U p)
    (t : {t : Fin (p + 1) → Fin m // StrictMono t}) :
    (finiteCoverOrderedCoordinates B f T U M p).hom x t =
      biproduct.π (fun a : Fin (p + 1) ↪o Fin m ↦
        (finiteCoverSectionPresheaf B f T M).obj (op (⨅ k, U (a k))))
        (OrderEmbedding.ofStrictMono t.1 t.2) x := by
  let A := fun a : Fin (p + 1) ↪o Fin m ↦
    (finiteCoverSectionPresheaf B f T M).obj (op (⨅ k, U (a k)))
  let a := OrderEmbedding.ofStrictMono t.1 t.2
  have h : (ModuleCat.biproductIsoPi A).hom ≫
      ModuleCat.ofHom (LinearMap.proj a : (∀ a, A a) →ₗ[B] A a) = biproduct.π A a := by
    apply (cancel_epi (ModuleCat.biproductIsoPi A).inv).1
    rw [Iso.inv_hom_id_assoc, ModuleCat.biproductIsoPi_inv_comp_π]
  exact ConcreteCategory.congr_hom h x

private theorem finiteCoverOrderedCoordinates_d (f : X ⟶ Y) (T : Y.Etale)
    {m : ℕ} (U : Fin m → X.Opens)
    (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)) (p : ℕ)
    (x : finiteCoverSectionTerm B f T M U p)
    (t : {t : Fin (p + 2) → Fin m // StrictMono t}) :
    (finiteCoverOrderedCoordinates B f T U M (p + 1)).hom
        (finiteCoverSectionDifferential B f T M U p x) t =
      ∑ j : Fin (p + 2), (-1 : ℤ) ^ (j : ℕ) •
        (finiteCoverSectionPresheaf B f T M).map
          (homOfLE (le_iInf fun k ↦
            iInf_le (fun l ↦ U (t.1 l)) (j.succAbove k))).op
          ((finiteCoverOrderedCoordinates B f T U M p).hom x
            ⟨t.1 ∘ j.succAbove, t.2.comp (Fin.strictMono_succAbove j)⟩) := by
  simpa only [finiteCoverOrderedCoordinates_apply] using!
    (finiteCoverSectionDifferential_π_apply B f T M U p x
      (OrderEmbedding.ofStrictMono t.1 t.2))

private def finiteCoverOrderedSectionComplex (f : X ⟶ Y) (T : Y.Etale)
    {m : ℕ} (U : Fin m → X.Opens)
    (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)) :
    CochainComplex (ModuleCat.{u + 1} B) ℕ :=
  CochainComplex.of (finiteCoverSectionTerm B f T M U)
    (finiteCoverSectionDifferential B f T M U)
    (finiteCoverSectionDifferential_squared B f T M U)

private def finiteCoverOrderedAbIso (f : X ⟶ Y) (T : Y.Etale)
    {m : ℕ} (U : Fin m → X.Opens)
    (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B))
    (A : CochainComplex AddCommGrpCat.{u + 1} ℕ)
    (e : ∀ p : ℕ, A.X p ≅ AddCommGrpCat.of
      (∀ t : {t : Fin (p + 1) → Fin m // StrictMono t},
        (finiteCoverSectionPresheaf B f T M).obj (op (⨅ k, U (t.1 k)))))
    (hd : ∀ (p : ℕ) (x : A.X p)
      (t : {t : Fin (p + 2) → Fin m // StrictMono t}),
      (e (p + 1)).hom (A.d p (p + 1) x) t =
        ∑ j : Fin (p + 2), (-1 : ℤ) ^ (j : ℕ) •
          (finiteCoverSectionPresheaf B f T M).map
            (homOfLE (le_iInf fun k ↦
              iInf_le (fun l ↦ U (t.1 l)) (j.succAbove k))).op
            ((e p).hom x ⟨t.1 ∘ j.succAbove,
              t.2.comp (Fin.strictMono_succAbove j)⟩)) :
    ((forget₂ (ModuleCat B) AddCommGrpCat).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (finiteCoverOrderedSectionComplex B f T U M) ≅ A :=
  HomologicalComplex.Hom.isoOfComponents
    (fun p ↦ finiteCoverOrderedCoordinates B f T U M p ≪≫ (e p).symm) (by
      rintro p q (rfl : p + 1 = q)
      apply (cancel_mono (e (p + 1)).hom).1
      simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc,
        Iso.inv_hom_id, Category.comp_id]
      apply AddCommGrpCat.ext
      intro x
      change finiteCoverSectionTerm B f T M U p at x
      funext t
      simp only [Functor.mapHomologicalComplex_obj_d, finiteCoverOrderedSectionComplex,
        CochainComplex.of_d, ModuleCat.forget₂_map, AddCommGrpCat.ofHom_apply,
        AddCommGrpCat.comp_apply]
      change (e (p + 1)).hom (A.d p (p + 1)
          ((e p).inv ((finiteCoverOrderedCoordinates B f T U M p).hom x))) t =
        (finiteCoverOrderedCoordinates B f T U M (p + 1)).hom
          (finiteCoverSectionDifferential B f T M U p x) t
      rw [hd, Iso.inv_hom_id_apply]
      exact (finiteCoverOrderedCoordinates_d B f T U M p x t).symm)

/-- Positive cocycle lifting in the actual ordered section complex.

Source: Stacks Project, Tags 03FB and 03FC, and Cohomology of Sheaves,
Tags 01FJ, 01FK and 01FM.
(blueprint: new-finite-cover-positive-rows-exact)

Proof: Regard M as a module presheaf on X_et. It is injective there because
module sheafification is an exact left adjoint (Tag 03FB). Let W be the
etale object X times_Y T, and let W_i be T times_Y U_i. The canonical
objects T times_Y the intersections of the U_i, with their restriction
maps, are the iterated products of the W_i in X_et/W: the universal
property follows by the pullback property and the universal property of
an intersection of open subobjects. Thus Tag 03FC, or the equivalent
injective-presheaf cocycle-lifting theorem, makes the full all-tuple
Cech complex exact in positive degrees. Use the ordered/full homotopy
comparison of Tags 01FJ, 01FK and 01FM for the presheaf on X.Opens sending
V to M(T times_Y V). Its intersections and maps are exactly those just
specified. The projection onto increasing tuples is a homotopy equivalence,
so the increasing-tuple complex also has zero positive homology. In each
degree the finite biproduct of modules is canonically their product, and
its projections give precisely the named finiteCoverSectionDifferential.
The elementwise ModuleCat exactness criterion therefore says that every
positive cocycle is the image of a cochain in the preceding degree, which
is the asserted exactness. No degree-zero gluing assertion is used in this
argument. Empty intersections and empty increasing-tuple index sets give
zero groups; in particular the statement holds for one-member covers and
the empty scheme. -/
theorem finite_open_cover_section_positive_exact
    (f : X ⟶ Y) (m : ℕ) (hm : 1 ≤ m) (U : Fin m → X.Opens) (hU : iSup U = ⊤)
    (T : Y.Etale) (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)) [Injective M]
    (p : ℕ) :
    (ShortComplex.mk (finiteCoverSectionDifferential B f T M U p)
      (finiteCoverSectionDifferential B f T M U (p + 1))
      (finiteCoverSectionDifferential_squared B f T M U p)).Exact := by
  haveI : Injective M.obj :=
    (sheafificationAdjunction X.smallEtaleTopology (ModuleCat.{u + 1} B)).map_injective
      M inferInstance
  have hf := CategoryTheory.Presheaf.exactAt_categoricalCech_of_injective M.obj
    (fun i ↦ (finiteCoverTestOverFunctor f T).obj (U i)) p
  change (finiteCoverFullTestComplex B f T U M).ExactAt (p + 1) at hf
  let G := forget₂ (ModuleCat.{u + 1} B) AddCommGrpCat
  have hfg : (G.mapHomologicalComplex (ComplexShape.up ℕ)).obj
      (finiteCoverFullTestComplex B f T U M) |>.ExactAt (p + 1) := by
    rw [HomologicalComplex.exactAt_iff' _ p (p + 1) (p + 2) (by simp) (by simp)] at hf ⊢
    exact hf.map G
  have hs := hfg.of_iso (finiteCoverFullTestAbIso B f T U M)
  obtain ⟨A, e, r, hd, hr, hi⟩ := Scheme.alternatingCechComputes X U hU
    (finiteCoverSectionPresheaf B f T M ⋙ G) (finiteCoverOpenCech U)
  haveI : IsIso (HomologicalComplex.homologyMap r (p + 1)) := hi (p + 1)
  haveI : QuasiIsoAt r (p + 1) :=
    (quasiIsoAt_iff_isIso_homologyMap r (p + 1)).2 inferInstance
  have hA := (exactAt_iff_of_quasiIsoAt r (p + 1)).1 hs
  have ho := hA.of_iso (finiteCoverOrderedAbIso B f T U M A e hd).symm
  rw [HomologicalComplex.exactAt_iff' _ p (p + 1) (p + 2) (by simp) (by simp)] at ho
  apply (ShortComplex.exact_iff_exact_map_forget₂ _).2
  rw [show p + 2 = (p + 1) + 1 by omega] at ho
  simpa only [HomologicalComplex.sc', HomologicalComplex.shortComplexFunctor',
    Functor.mapHomologicalComplex_obj_d, Functor.mapHomologicalComplex_obj_X,
    finiteCoverOrderedSectionComplex, CochainComplex.of_d, ShortComplex.map] using! ho

/-- Positive section acyclicity implies exactness of the named sheaf-valued row.
Source: Stacks Project, Tag 03AZ. Apply the section acyclicity theorem to the
injective evaluated term. The proved comparison of short complexes transfers
exactness to every section group. Exact sheafification and evaluation then give
exactness in the functor category.
(blueprint: new-finite-cover-positive-rows-exact) -/
theorem finite_open_cover_positive_rows_exact
    (f : X ⟶ Y) (m : ℕ) (hm : 1 ≤ m) (U : Fin m → X.Opens) (hU : iSup U = ⊤)
    (J : CochainComplex
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B) ⥤
        Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)) ℕ)
    (hI : ∀ (q : ℕ) (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)),
      Injective ((J.X q).obj M))
    (data : finiteOpenCoverOrderedData B f m U J) :
    (∀ (p q : ℕ), (ShortComplex.mk
      (((finiteOpenCoverResolutionDoubleComplex B f m U J data.hB data.hComm data.hSq).d
        p (p + 1)).f q)
      (((finiteOpenCoverResolutionDoubleComplex B f m U J data.hB data.hComm data.hSq).d
        (p + 1) (p + 2)).f q)
      (by rw [← HomologicalComplex.comp_f, HomologicalComplex.d_comp_d,
        HomologicalComplex.zero_f])).Exact) := by
  intro p q
  change (finiteCoverPositiveRow B f U J data p q).Exact
  rw [ShortComplex.exact_iff_evaluation]
  intro M
  apply finiteCoverSheafExact_of_sections
  intro T
  letI := hI q M
  exact ShortComplex.exact_of_iso
    (finiteCoverPositiveRowSectionsIso B f U J data T M p q).symm
    (finite_open_cover_section_positive_exact B f m hm U hU T ((J.X q).obj M) p)

end AlgebraicGeometry.Etale
