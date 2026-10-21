/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups Q128 and X5
-/
module

public import Sheaf.Algebra.Homology.KoszulRoosComparisonData
import WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimitRange
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Homology.KoszulRoosNormalizedModels
import Sheaf.Algebra.Homology.KoszulRoosCoefficientCompatibility

/-! # Koszul tensor, finite tails, and normalized Roos projection adjoints

Source: blueprint main-20261015, sec-smooth-purity/sk-lem-sp-tower, proof paragraph 1.
(blueprint: lem-sp-koszul-roos-projection-comparison)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u v r w t z
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped ChangeOfRings

namespace CategoryTheory.KoszulRoos

attribute [local instance] SheafOfModules.isMonoidal_W_independentCoefficients
attribute [local instance] SheafOfModules.monoidalCategory

private theorem constant_identification {A : Type*} [Category A] [Abelian A]
    [HasCountableProducts A] [HasDerivedCategory.{w} A]
    (N : CochainComplex A ℤ) :
    IsIso (DerivedCategory.Q.map (roosEval
      (((Functor.const ℕᵒᵖ).mapHomologicalComplex (.up ℤ)).obj N) 0)) ∧
    ∃ diagonal : N ⟶ roosF.obj (((Functor.const ℕᵒᵖ).mapHomologicalComplex (.up ℤ)).obj N),
      (∀ q : ℤ, diagonal.f (q + 1) ≫
        (roosχ (((Functor.const ℕᵒᵖ).mapHomologicalComplex (.up ℤ)).obj N) q).hom =
        biprod.lift 0 ((Pi.lift (fun _ : ℕ ↦ 𝟙 N)).f (q + 1))) ∧
      DerivedCategory.Q.map diagonal ≫
          DerivedCategory.Q.map (roosEval
            (((Functor.const ℕᵒᵖ).mapHomologicalComplex (.up ℤ)).obj N) 0) = 𝟙 _ ∧
      DerivedCategory.Q.map (roosEval
        (((Functor.const ℕᵒᵖ).mapHomologicalComplex (.up ℤ)).obj N) 0) ≫
          DerivedCategory.Q.map diagonal = 𝟙 _ := by
  let X := ((Functor.const ℕᵒᵖ).mapHomologicalComplex (.up ℤ)).obj N
  let P := roosP X
  let p (n : ℕ) : P ⟶ N := Pi.π (fun i : ℕ ↦ X.asFunctor.obj (op i)) n
  let d : N ⟶ P := Pi.lift (fun _ : ℕ ↦ 𝟙 N)
  let u : P ⟶ P := roosU X
  have hu (n : ℕ) : u ≫ p n = p n - p (n + 1) := by
    have h := (towerTransitionEndomorphism_eq_iff
      (fun j : ℕ ↦ X.asFunctor.map (homOfLE (Nat.le_succ j)).op) u).1 rfl n
    change u ≫ p n = p n - (p (n + 1) ≫ 𝟙 N) at h
    exact h.trans (congrArg (fun z ↦ p n - z) (Category.comp_id (p (n + 1))))
  let a : ℕ → (P ⟶ N) := fun n ↦ Nat.rec 0 (fun n b ↦ b - p n) n
  let v : P ⟶ P := Pi.lift a
  have hvu : v ≫ u = 𝟙 P := by
    apply Pi.hom_ext
    intro n
    change (v ≫ u) ≫ p n = 𝟙 P ≫ p n
    rw [Category.assoc, hu, Preadditive.comp_sub]
    simp only [v, p, Pi.lift_π, Category.id_comp]
    change a n - (a n - p n) = p n
    abel
  have huv : u ≫ v = 𝟙 P - p 0 ≫ d := by
    apply Pi.hom_ext
    intro n
    change (u ≫ v) ≫ p n = (𝟙 P - p 0 ≫ d) ≫ p n
    simp only [v, p, d, Pi.lift_π, Category.assoc, Preadditive.sub_comp,
      Category.id_comp, Category.comp_id]
    change u ≫ a n = p n - p 0
    induction n with
    | zero => simp [a]
    | succ n ih =>
      change u ≫ (a n - p n) = _
      rw [Preadditive.comp_sub, ih, hu]
      abel
  have hdiag : d ≫ u = 0 := by
    apply Pi.hom_ext
    intro n
    change (d ≫ u) ≫ p n = 0 ≫ p n
    rw [Category.assoc, hu, Preadditive.comp_sub]
    simp [d, p]
  let diagonal : N ⟶ roosF.obj X := roosLift d hdiag
  have hd : diagonal ≫ roosProj X = d := by
    exact CochainComplex.mappingCocone.lift_fst _ _ _ _
  have he : diagonal ≫ roosEval X 0 = 𝟙 N := by
    rw [roosEval, ← Category.assoc, hd]
    simp [d]
  let T := DerivedCategory.Q.mapTriangle.obj (CochainComplex.mappingCocone.triangle u)
  have hT : T ∈ distTriang _ :=
    DerivedCategory.mappingCocone_triangle_distinguished u
  have hsplit : SplitEpi (DerivedCategory.Q.map u) :=
    ⟨DerivedCategory.Q.map v, by rw [← Functor.map_comp, hvu, Functor.map_id]⟩
  have hepi : Epi T.mor₂ := by
    change Epi (DerivedCategory.Q.map u)
    exact hsplit.epi
  have hmono : Mono (DerivedCategory.Q.map (roosProj X)) :=
    T.mono₁ hT (T.mor₃_eq_zero_of_epi₂ hT hepi)
  let := hmono
  have hother : DerivedCategory.Q.map (roosEval X 0) ≫
      DerivedCategory.Q.map diagonal = 𝟙 _ := by
    apply (cancel_mono (DerivedCategory.Q.map (roosProj X))).1
    rw [Category.assoc, ← Functor.map_comp, hd, Category.id_comp]
    rw [roosEval, Functor.map_comp, Category.assoc, ← Functor.map_comp]
    have hz : DerivedCategory.Q.map (roosProj X) ≫ DerivedCategory.Q.map u = 0 :=
      Pretriangulated.comp_distTriang_mor_zero₁₂ T hT
    have hcalc : DerivedCategory.Q.map (roosProj X) ≫
        DerivedCategory.Q.map (p 0 ≫ d) = DerivedCategory.Q.map (roosProj X) := by
      have hh := congrArg (fun f ↦ DerivedCategory.Q.map (roosProj X) ≫
        DerivedCategory.Q.map f) huv
      rw [Functor.map_comp, ← Category.assoc, hz, zero_comp, Functor.map_sub,
        Functor.map_id, Preadditive.comp_sub, Category.comp_id] at hh
      exact (sub_eq_zero.mp hh.symm).symm
    exact hcalc
  have hfirst : DerivedCategory.Q.map diagonal ≫
      DerivedCategory.Q.map (roosEval X 0) = 𝟙 _ := by
    rw [← Functor.map_comp, he, Functor.map_id]
  have hiso : IsIso (DerivedCategory.Q.map (roosEval X 0)) :=
    ⟨⟨DerivedCategory.Q.map diagonal, hother, hfirst⟩⟩
  exact ⟨hiso, diagonal, fun q ↦ roosLift_χ d hdiag q, hfirst, hother⟩

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [HasSheafify J AddCommGrpCat.{r}] [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
  (R : Sheaf J CommRingCat.{r})
  (s : (R.obj ⋙ forget CommRingCat.{r}).sections) [HasSheafify J CommRingCat.{r}]
  [∀ S : Sheaf J CommRingCat.{r}, HasDerivedCategory.{w} (Modules S)]
  [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ Modules R)]

private theorem endoPow_add {D : Type*} [Category D] {A : D} (f : A ⟶ A)
    (i j : ℕ) : endoPow f (i + j) = endoPow f i ≫ endoPow f j := by
  induction j with
  | zero => simp [endoPow]
  | succ j ih => simpa [endoPow, Category.assoc] using congrArg (· ≫ f) ih

omit [HasSheafify J CommRingCat]
  [∀ S : Sheaf J CommRingCat.{r}, HasDerivedCategory.{w} (Modules S)]
  [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ Modules R)] in
private theorem koszulStep_formula (k m : ℕ) (hkm : k ≤ m) :
    ∃ square :
      (CochainComplex.singleFunctor (Modules R) 0).map
          (endoPow (globalSectionMultiplication R (unitSection R s)) (m + 1)) ≫ 𝟙 _ =
        (CochainComplex.singleFunctor (Modules R) 0).map
            (endoPow (globalSectionMultiplication R (unitSection R s)) (m - k)) ≫
          (CochainComplex.singleFunctor (Modules R) 0).map
            (endoPow (globalSectionMultiplication R (unitSection R s)) (k + 1)),
      koszulStep R s hkm = CochainComplex.mappingCone.map _ _
        ((CochainComplex.singleFunctor (Modules R) 0).map
          (endoPow (globalSectionMultiplication R (unitSection R s)) (m - k)))
        (𝟙 _) square := by
  let F := CochainComplex.singleFunctor (Modules R) 0
  let a := globalSectionMultiplication R (unitSection R s)
  have square (k m : ℕ) (h : k ≤ m) :
      F.map (endoPow a (m + 1)) ≫ 𝟙 _ =
        F.map (endoPow a (m - k)) ≫ F.map (endoPow a (k + 1)) := by
    rw [Category.comp_id, ← F.map_comp, ← endoPow_add]
    congr 2
    omega
  refine ⟨square k m hkm, ?_⟩
  induction m, hkm using Nat.le_induction with
  | base =>
    simp [koszulStep, principalKoszulTower, endoPow,
      CochainComplex.mappingCone.map_id, principalKoszul]
  | succ m hkm ih =>
    have hcomp : koszulStep R s (Nat.le_trans hkm (Nat.le_succ m)) =
        principalKoszulTransition R (unitSection R s) m ≫ koszulStep R s hkm := by
      unfold koszulStep
      rw [show (homOfLE (Nat.le_trans hkm (Nat.le_succ m))).op =
        (homOfLE (Nat.le_succ m)).op ≫ (homOfLE hkm).op from Subsingleton.elim _ _]
      rw [Functor.map_comp]
      congr 1
      exact Functor.ofOpSequence_map_homOfLE_succ _ m
    rw [hcomp, ih]
    dsimp only [principalKoszulTransition]
    rw [← CochainComplex.mappingCone.map_comp]
    congr 1
    · rw [← F.map_comp]
      have hadd : endoPow a (m + 1 - k) = a ≫ endoPow a (m - k) := by
        have hn : m + 1 - k = 1 + (m - k) := by omega
        rw [hn, endoPow_add]
        simp [endoPow]
      exact congrArg F.map hadd.symm

private theorem comparison_isIso (M : Models R s) (hM : Normalization R s M)
    (X : CochainComplex (ℕᵒᵖ ⥤ Modules R) ℤ) (m h : ℕ) :
    IsIso (M.comparison R s X m h) := by
  have := hM.delete_quasiIso ((onTowers R (tensor R s m)).obj X) h
  dsimp only [Models.comparison]
  infer_instance

private theorem comparison_natural (M : Models R s) (hM : Normalization R s M)
    {X Y : CochainComplex (ℕᵒᵖ ⥤ Modules R) ℤ} (f : X ⟶ Y) (m h : ℕ) :
    ((M.scalar m).T ⋙ (restriction R s m).mapDerivedCategory).map
        (M.RF.map (DerivedCategory.Q.map f)) ≫ M.comparison R s Y m h =
      M.comparison R s X m h ≫ M.RF.map (DerivedCategory.Q.map
        ((tail R h).map ((onTowers R (tensor R s m)).map f))) := by
  let H := (M.scalar m).T ⋙ (restriction R s m).mapDerivedCategory
  dsimp only [Models.comparison]
  have hn := M.norm.inv.naturality f
  simp only [Functor.comp_map] at hn
  rw [← H.map_comp_assoc, hn, H.map_comp_assoc]
  have hA := (M.A m).inv.naturality (roosF.map f)
  simp only [Functor.comp_map] at hA
  erw [reassoc_of% hA]
  have hχ := (M.chi m).hom.naturality f
  simp only [Functor.comp_map] at hχ
  rw [← DerivedCategory.Q.map_comp_assoc]
  erw [hχ]
  simp only [Functor.map_comp, Category.assoc]
  have hd := congrArg DerivedCategory.Q.map
    (hM.delete_natural ((onTowers R (tensor R s m)).map f) h)
  simp only [Functor.map_comp] at hd
  rw [reassoc_of% hd]
  have he := M.norm.hom.naturality
    ((tail R h).map ((onTowers R (tensor R s m)).map f))
  simp only [Functor.comp_map] at he
  rw [he]


omit [HasSheafify J CommRingCat]
  [∀ S : Sheaf J CommRingCat.{r}, HasDerivedCategory.{w} (Modules S)]
  [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ Modules R)] in
private theorem tensor_hom_ext (m : ℕ) (P : CochainComplex (Modules R) ℤ)
    {q : ℤ} {Y : Modules R} (f g : ((tensor R s m).obj P).X q ⟶ Y)
    (h : ∀ (a b : ℤ) (hab : a + b = q),
      summand R s m P a b q hab ≫ f = summand R s m P a b q hab ≫ g) : f = g := by
  apply HomologicalComplex.mapBifunctor.hom_ext
    (K₁ := K R s m) (K₂ := P) (F := curriedTensor (Modules R))
  intro a b hab
  exact h a b hab

private theorem chi_eval (M : Models R s) (hM : Normalization R s M)
    (m : ℕ) (X : CochainComplex (ℕᵒᵖ ⥤ Modules R) ℤ) (n : ℕ) :
    (M.chi m).hom.app X ≫ roosEval ((onTowers R (tensor R s m)).obj X) n =
      (tensor R s m).map (roosEval X n) := by
  with_unfolding_all
    ext q : 1
    apply tensor_hom_ext R s m (roosF.obj X)
    intro a b hab
    subst q
    have heval (Y : CochainComplex (ℕᵒᵖ ⥤ Modules R) ℤ) (q : ℤ) :
        (roosEval Y n).f q =
          (coordinates R Y q).hom ≫ biprod.snd ≫
            (Pi.π (fun i : ℕ ↦ Y.asFunctor.obj (op i)) n).f q := by
      have hc : (coordinates R Y q).hom ≫ biprod.snd = (roosProj Y).f q := by
        dsimp only [coordinates, Iso.trans_hom, biprod.mapIso_hom, Iso.refl_hom]
        simp only [Category.assoc, biprod.map_snd]
        rw [← reassoc_of% (roosProj_f Y (q - 1))]
        rw [← Category.assoc, ← HomologicalComplex.XIsoOfEq_hom_naturality]
        rw [Category.assoc, HomologicalComplex.XIsoOfEq_hom_comp_XIsoOfEq_hom]
        simp only [HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom, Category.comp_id]
      simpa only [roosEval, HomologicalComplex.comp_f, Category.assoc] using
        congrArg (fun f ↦ f ≫ (Pi.π (fun i : ℕ ↦ Y.asFunctor.obj (op i)) n).f q)
          hc.symm
    simp only [HomologicalComplex.comp_f, heval]
    rw [reassoc_of% (hM.chi_second m X a b)]
    have hp := congrArg (fun f ↦ f.f (a + b))
      (Pi.lift_π (fun j : ℕ ↦ (tensor R s m).map
        (Pi.π (fun i : ℕ ↦ X.asFunctor.obj (op i)) j)) n)
    dsimp only [HomologicalComplex.comp_f] at hp
    erw [show (tensorProduct R s m X).f (a + b) ≫
      (Pi.π (fun i : ℕ ↦
        ((onTowers R (tensor R s m)).obj X).asFunctor.obj (op i)) n).f (a + b) =
      ((tensor R s m).map (Pi.π (fun i : ℕ ↦ X.asFunctor.obj (op i)) n)).f
        (a + b) from hp]
    dsimp only [summand, tensor, Functor.map₂CochainComplex,
      Functor.map₂HomologicalComplex]
    simp only [HomologicalComplex.ι_mapBifunctorMap, HomologicalComplex.id_f,
      Functor.map_id, NatTrans.id_app, Category.id_comp]
    rw [heval]
    simp only [MonoidalCategory.curriedTensor_obj_map,
      MonoidalCategory.whiskerLeft_comp, Category.assoc]

private theorem comparison_projection (M : Models R s) (hM : Normalization R s M)
    (X : CochainComplex (ℕᵒᵖ ⥤ Modules R) ℤ) (m h n : ℕ) :
    M.comparison R s X m h ≫
        M.projection R s ((tail R h).obj ((onTowers R (tensor R s m)).obj X)) n =
      ((M.scalar m).T ⋙ (restriction R s m).mapDerivedCategory).map
          (M.projection R s X (h + n)) ≫
        (M.A m).inv.app (X.asFunctor.obj (op (h + n))) := by
  let H := (M.scalar m).T ⋙ (restriction R s m).mapDerivedCategory
  simp only [Models.comparison, Models.projection, Category.assoc,
    Iso.hom_inv_id_app_assoc]
  rw [← DerivedCategory.Q.map_comp, hM.delete_projection]
  rw [← DerivedCategory.Q.map_comp, chi_eval R s M hM]
  have hn := (M.A m).inv.naturality (roosEval X (h + n))
  simp only [Functor.comp_map] at hn
  rw [H.map_comp]
  with_unfolding_all
    simpa only [H, Functor.comp_map, Category.assoc] using
      congrArg (fun f ↦ H.map (M.norm.inv.app X) ≫ f) hn.symm

private theorem comparison_bounded (M : Models R s) (hM : Normalization R s M)
    (X : CochainComplex (ℕᵒᵖ ⥤ Modules R) ℤ) (a b : ℤ)
    (hX : ∀ (n : ℕ) (q : ℤ), q < a ∨ b < q →
      IsZero ((DerivedCategory.homologyFunctor (Modules R) q).obj
        (DerivedCategory.Q.obj (X.asFunctor.obj (op n)))))
    (q : ℤ) (hq : q < a ∨ b + 1 < q) :
    IsZero ((DerivedCategory.homologyFunctor (Modules R) q).obj
      (M.RF.obj (DerivedCategory.Q.obj X))) := by
  let := hM.exactProducts
  have hP (i : ℤ) (hi : i < a ∨ b < i) :
      IsZero ((DerivedCategory.homologyFunctor (Modules R) i).obj
        (DerivedCategory.Q.obj (roosP X))) := by
    let H := HomologicalComplex.homologyFunctor (Modules R) (.up ℤ) i
    have hn (n : ℕ) : IsZero (H.obj (X.asFunctor.obj (op n))) :=
      (hX n i hi).of_iso ((DerivedCategory.homologyFunctorFactors (Modules R) i).app
        (X.asFunctor.obj (op n))).symm
    have hlim := isLimitOfPreserves H
      (productIsProduct (fun n : ℕ ↦ X.asFunctor.obj (op n)))
    have hz : IsZero (H.obj (roosP X)) := by
      apply (IsZero.iff_id_eq_zero _).2
      apply hlim.hom_ext
      intro n
      exact (hn n.as).eq_of_tgt _ _
    exact hz.of_iso ((DerivedCategory.homologyFunctorFactors (Modules R) i).app (roosP X))
  let T := DerivedCategory.Q.mapTriangle.obj (CochainComplex.mappingCocone.triangle (roosU X))
  have hT : T ∈ distTriang _ :=
    DerivedCategory.mappingCocone_triangle_distinguished (roosU X)
  have hz : IsZero ((DerivedCategory.homologyFunctor (Modules R) q).obj
      (DerivedCategory.Q.obj (roosF.obj X))) :=
    (DerivedCategory.HomologySequence.exact₁ T hT (q - 1) q (by omega)).isZero_of_both_isZero
      (hP (q - 1) (by rcases hq with h | h <;> omega))
      (hP q (by rcases hq with h | h <;> omega))
  exact hz.of_iso
    ((DerivedCategory.homologyFunctor (Modules R) q).mapIso (M.norm.app X)).symm

private theorem augmentation_adjoint (M : Models R s) (hM : Normalization R s M)
    (m : ℕ) (P : CochainComplex (Modules R) ℤ)
    (N : CochainComplex (Modules (B R s m)) ℤ)
    (f : ((M.scalar m).E.mapHomologicalComplex (.up ℤ)).obj P ⟶ N) :
    (M.A m).inv.app P ≫ DerivedCategory.Q.map ((M.aug m).app P) ≫
        DerivedCategory.Q.map ((restrictComplex R s m).map f) =
      (restriction R s m).mapDerivedCategory.map
        (((M.derivedAdj m).homEquiv _ _).symm
          (DerivedCategory.Q.map
              (((M.ordinaryAdj m).mapHomologicalComplex (.up ℤ)).homEquiv P N f) ≫
            (restriction R s m).mapDerivedCategoryFactors.inv.app N)) ≫
        (restriction R s m).mapDerivedCategoryFactors.hom.app N := by
  let V := (restriction R s m).mapDerivedCategory
  let E := (M.scalar m).E.mapHomologicalComplex (.up ℤ)
  let O := (M.ordinaryAdj m).mapHomologicalComplex (.up ℤ)
  have hkflat (L : CochainComplex (Modules R) ℤ)
      (hL : CochainComplex.IsKFlatIndependentCoefficients (R := R) L)
      (g : E.obj L ⟶ N) :
      (M.A m).inv.app L ≫ DerivedCategory.Q.map ((M.aug m).app L) ≫
          DerivedCategory.Q.map ((restrictComplex R s m).map g) =
        V.map (((M.derivedAdj m).homEquiv _ _).symm
          (DerivedCategory.Q.map (O.homEquiv L N g) ≫
            (restriction R s m).mapDerivedCategoryFactors.inv.app N)) ≫
          (restriction R s m).mapDerivedCategoryFactors.hom.app N := by
    rw [hM.derived_adjunction m L hL N g]
    rw [Functor.map_comp, Category.assoc,
      (restriction R s m).mapDerivedCategoryFactors_hom_naturality]
    rw [← Category.assoc, ← hM.A_kflat m L hL]
    simp
    rfl
  obtain ⟨L, q, hL, _, hq, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients (R := R) P
  let := hq
  have hQ : IsIso (DerivedCategory.Q.map q) := inferInstance
  have hH : IsIso (((M.scalar m).T ⋙ V).map (DerivedCategory.Q.map q)) := inferInstance
  apply (cancel_epi (((M.scalar m).T ⋙ V).map (DerivedCategory.Q.map q))).1
  have hA : ((M.scalar m).T ⋙ V).map (DerivedCategory.Q.map q) ≫
      (M.A m).inv.app P =
    (M.A m).inv.app L ≫ DerivedCategory.Q.map ((tensor R s m).map q) :=
    (M.A m).inv.naturality q
  rw [← Category.assoc, ← Category.assoc, hA]
  simp only [Category.assoc]
  have ha := (M.aug m).naturality q
  simp only [Functor.comp_map] at ha
  rw [← DerivedCategory.Q.map_comp_assoc, ha, DerivedCategory.Q.map_comp_assoc]
  rw [← DerivedCategory.Q.map_comp]
  change (M.A m).inv.app L ≫ DerivedCategory.Q.map ((M.aug m).app L) ≫
      DerivedCategory.Q.map ((restrictComplex R s m).map (E.map q ≫ f)) = _
  rw [hkflat L hL (E.map q ≫ f), O.homEquiv_naturality_left,
    DerivedCategory.Q.map_comp, Category.assoc,
    (M.derivedAdj m).homEquiv_naturality_left_symm, V.map_comp]
  dsimp only [V, O]
  simp only [Functor.comp_map, Category.assoc]

private theorem comparison_adjoint (M : Models R s) (hM : Normalization R s M) :
    ∀ (X : CochainComplex (ℕᵒᵖ ⥤ Modules R) ℤ) (m : ℕ)
    (N : CochainComplex (Modules (B R s m)) ℤ)
    (f : ((tail R m).obj X).asFunctor ⋙
      (M.scalar m).E.mapHomologicalComplex (.up ℤ) ⟶ (Functor.const ℕᵒᵖ).obj N),
    M.comparison R s X m m ≫
        M.RF.map (DerivedCategory.Q.map (M.familyMap R s X m N f)) ≫
        M.norm.inv.app (constant R ((restrictComplex R s m).obj N)) ≫
        DerivedCategory.Q.map (roosEval (constant R ((restrictComplex R s m).obj N)) 0) =
      (restriction R s m).mapDerivedCategory.map
        (((M.derivedAdj m).homEquiv _ _).symm
          (M.projection R s X m ≫
            DerivedCategory.Q.map
              (((M.ordinaryAdj m).mapHomologicalComplex (.up ℤ)).homEquiv
                (X.asFunctor.obj (op m)) N (f.app (op 0))) ≫
            (restriction R s m).mapDerivedCategoryFactors.inv.app N)) ≫
        (restriction R s m).mapDerivedCategoryFactors.hom.app N := by
  intro X m N f
  let Y := (tail R m).obj ((onTowers R (tensor R s m)).obj X)
  let Z := constant R ((restrictComplex R s m).obj N)
  let H := (M.scalar m).T ⋙ (restriction R s m).mapDerivedCategory
  have hfamily :
      (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map
        (M.familyMap R s X m N f)).app (op 0) =
      (M.aug m).app (X.asFunctor.obj (op m)) ≫
        (restrictComplex R s m).map (f.app (op 0)) := by
    rfl
  have hn := M.norm.inv.naturality (M.familyMap R s X m N f)
  simp only [Functor.comp_map] at hn
  rw [reassoc_of% hn]
  rw [← DerivedCategory.Q.map_comp, roosEval_natural, DerivedCategory.Q.map_comp, hfamily]
  have hp := comparison_projection R s M hM X m m 0
  dsimp only [Models.projection] at hp
  simp only [Nat.add_zero] at hp
  rw [reassoc_of% hp]
  rw [DerivedCategory.Q.map_comp ((M.aug m).app (X.asFunctor.obj (op m)))
    ((restrictComplex R s m).map (f.app (op 0)))]
  rw [augmentation_adjoint R s M hM]
  rw [← Functor.map_comp_assoc,
    ← (M.derivedAdj m).homEquiv_naturality_left_symm]
  rfl

private theorem compatibility_of_normalization (M : Models R s)
    (hM : Normalization R s M)
    (hc : ∀ (k m : ℕ) (hkm : k ≤ m),
    ∃ q : B R s m ⟶ B R s k,
      quotient R s m ≫ q = quotient R s k ∧
      ∃ e : (M.scalar m).E ⋙ restriction R s m ⟶
          (M.scalar k).E ⋙ restriction R s k,
        (∀ (P : Modules R) (U : Cᵒᵖ) (b : (B R s m).obj.obj U) (x : P.val.obj U),
          (e.app P).val.app U (pure R s m (M.scalar m) P U b x) =
            pure R s k (M.scalar k) P U ((q.hom.app U).hom b) x) ∧
        ∃ c : (M.scalar m).T ⋙ (restriction R s m).mapDerivedCategory ⟶
            (M.scalar k).T ⋙ (restriction R s k).mapDerivedCategory,
          (∀ (P : CochainComplex (Modules R) ℤ),
            CochainComplex.IsKFlatIndependentCoefficients (R := R) P →
            c.app (DerivedCategory.Q.obj P) ≫
                (restriction R s k).mapDerivedCategory.map ((M.scalar k).ε.app P) ≫
                (restriction R s k).mapDerivedCategoryFactors.hom.app
                  (((M.scalar k).E.mapHomologicalComplex (.up ℤ)).obj P) =
              (restriction R s m).mapDerivedCategory.map ((M.scalar m).ε.app P) ≫
                (restriction R s m).mapDerivedCategoryFactors.hom.app
                  (((M.scalar m).E.mapHomologicalComplex (.up ℤ)).obj P) ≫
                DerivedCategory.Q.map
                  ((ordinaryTransition R s (M.scalar m) (M.scalar k) e).app P)) ∧
          (∀ P : CochainComplex (Modules R) ℤ,
            (tensorStep R s hkm).app P ≫ (M.aug k).app P =
              (M.aug m).app P ≫ (ordinaryTransition R s (M.scalar m) (M.scalar k) e).app P) ∧
          (∀ P : CochainComplex (Modules R) ℤ,
            DerivedCategory.Q.map ((tensorStep R s hkm).app P) ≫ (M.A k).hom.app P =
              (M.A m).hom.app P ≫ c.app (DerivedCategory.Q.obj P)) ∧
          (∀ (X : CochainComplex (ℕᵒᵖ ⥤ Modules R) ℤ) (h : ℕ),
            c.app (M.RF.obj (DerivedCategory.Q.obj X)) ≫ M.comparison R s X k h =
              M.comparison R s X m h ≫ M.RF.map (DerivedCategory.Q.map
                ((tail R h).map ((onTowersMap R (tensorStep R s hkm)).app X))))) :
    Compatibility R s M := by
  exact {
    toNormalization := hM
    isIso := comparison_isIso R s M hM
    projection := comparison_projection R s M hM
    constant_identification := by
      intro N
      exact constant_identification N
    adjoint := comparison_adjoint R s M hM
    koszul_transition := koszulStep_formula R s
    coefficients := hc
    natural := comparison_natural R s M hM
    bounded := comparison_bounded R s M hM }

/-- Koszul tensor and finite-tail comparison preserve the actual Roos projections,
strict augmentation adjoints, coefficient transitions, and uniform cohomological bounds.
The coefficient universe contains the small pro-etale site; its object and morphism
universes remain independent. The localization instances only select morphism sizes.

Source: blueprint main-20261015, sec-smooth-purity/sk-lem-sp-tower.proof.md,
paragraph 1; Bhatt--Scholze, Sections 3.1 and 3.5; Stacks 0941, 06YY and 09T5.
(blueprint: lem-sp-koszul-roos-projection-comparison)

Proof, following all thirteen DAG steps:

1. Work on the small pro-étale site in a module universe containing its objects. Countable
products of $R$-module sheaves are sectionwise and exact by
[lem-weil-proetale-countable-products-exact], for arbitrary $T$. Exactness implies $H^q(\prod
X_n)=\prod H^q(X_n)$: the product functor preserves the kernels and images defining cohomology.
Choose individual K-injective resolutions using [prop-pur-kinjective-resolutions-exist]. Their
product represents the derived product by [lem-pc-ringed-space-product-kinjective], and the map
from the product of the original complexes is a quasi-isomorphism by the preceding cohomology
equality. Thus termwise products represent derived products. The normalized natural comparison
[lem-weil-strict-roos-comparison] identifies the strict Roos fibre with the actual $H=R\!\lim
X_\bullet$, carries its coordinate maps to $p_n$, and identifies strict maps of Roos fibres with
derived-limit maps. We use this normalization throughout, also after reindexing a tail by
$\mathbf N_{\geq1}$. Dependencies: lem-weil-proetale-countable-products-exact,
prop-pur-kinjective-resolutions-exist, lem-pc-ringed-space-product-kinjective,
lem-weil-strict-roos-comparison.

2. Fix the following coordinates, using [def-weil-abstract-derived-category] and
[def-pc-tensor-complex-sheaves]. For a chain endomorphism $u:P\to P$, write $F_u^q=P^q\oplus
P^{q-1}$ with $d(x,y)=(dx,ux-dy)$. The map $(x,y)\mapsto(-y,x)$ identifies this with
$\operatorname{Cone}(u)[-1]$; projection is $(x,y)\mapsto x$. Put $D_m(C)=C\otimes_RK_m$. In
degree $q$ write its coordinates as $(a,b)\in C^q\oplus C^{q+1}$. The total differential is
$d(a,b)=(da+(-1)^{q+1}t^m b,db)$. Consequently $(a,b)\mapsto(a,(-1)^{q+1}b)$ is a chain
isomorphism $D_m(C)\cong\operatorname{Cone}(t^m:C\to C)$, carrying the inclusion of $C$ to the
cone inclusion and the augmentation to $a\mapsto a\otimes1$. These formulas fix all signs used
below. Dependencies: def-weil-abstract-derived-category, def-pc-tensor-complex-sheaves.

3. Multiplication by $t^m$ is injective, being a composite of $m$ injective maps, and $B_m$ is
its sheaf cokernel. Hence $0\to R\xrightarrow{t^m}R\to B_m\to0$ is exact. Apply
[lem-cbc-regular-quotient-cone-augmentation] with $r=t^m$ and $S=B_m$. Together with the
coordinate isomorphism in step 2 this gives a natural isomorphism
$A_{m,C}:QD_m(C)\xrightarrow{\sim}\operatorname{Res}(QC\otimes_R^LB_m)$. For a K-flat $P$,
$A_{m,P}$ is represented by the augmentation $P\otimes K_m\to\operatorname{Res}(P\otimes B_m)$,
and the inclusion $P\to D_m(P)$ becomes $p\mapsto p\otimes1$. The derived scalar extension is
computed on these resolutions by [lem-pur-derived-change-of-rings]. The same cited cone theorem
gives naturality for all derived morphisms and resolution independence. In particular $D_m$
preserves quasi-isomorphisms, since its localized cone functor exists on $D(R)$, or directly by
the cone cohomology sequence. Dependencies: lem-cbc-regular-quotient-cone-augmentation,
lem-pur-derived-change-of-rings.

4. Delete the coordinates $n<h$ in both copies of the product. This strictly commutes with
$1-s$, hence defines $F_{1-s}(\prod_{n\geq1}X_n)\to F_{1-s}(\prod_{n\geq h}X_n)$. It is
degreewise split surjective, and its kernel is $F_U(P_{<h})$, where $P_{<h}=\prod_{1\leq
n<h}X_n$, $U=1-s_{<h}$, and the shift on the finite prefix has zero last component. It is
nilpotent: $s_{<h}^{h-1}=0$ for $h>1$. Thus $U^{-1}=\sum_{j=0}^{h-2}s_{<h}^j$. On the kernel the
degree $-1$ map $(x,y)\mapsto(U^{-1}y,0)$ satisfies $dH+Hd=1$, since $U$ commutes with $d$. The
kernel is therefore acyclic. The long exact sequence
[lem-weil-pbc-complex-ses-homology-long-exact] proves the deletion map is a quasi-isomorphism.
For $h=1$ it is the identity and its kernel is zero. Every retained projection is unchanged
literally. Dependencies: def-weil-abstract-derived-category,
lem-weil-pbc-complex-ses-homology-long-exact.

5. Let $P=\prod_nX_n$. The canonical map $D_m(P)\to\prod_nD_m(X_n)$ is the chain isomorphism $(
(a_n)_n,(b_n)_n )\mapsto((a_n,b_n))_n$. Its inverse takes the two coordinate families. This is a
sheaf map: products are sectionwise and only two summands occur in every total degree. The
differential in step 2 is componentwise, so this permutation commutes with $d$. If
$s((a_n))=(v_na_{n+1})$ for the transition maps $v_n$, it also commutes with $s$ and therefore
with $1-s$. It commutes with every product projection, all strict tower maps, and deletion of
any prefix, as each of these acts on the same coordinates. Dependencies:
def-pc-tensor-complex-sheaves, lem-weil-proetale-countable-products-exact.

6. Tensor the fibre coordinates of step 2. For any $u:P\to P$, a degree $q$ element of
$D_m(F_u)$ has coordinates $(x,y,z,w)\in P^q\oplus P^{q-1}\oplus P^{q+1}\oplus P^q$. Send it to
$((x,z),(y,w))\in F_{D_m(u)}^q$. Both differentials, in the target ordering, are
$$((dx+(-1)^{q+1}t^m z,dz),(ux-dy+(-1)^{q+1}t^m w,uz-dw)).$$ Thus this permutation is a chain
isomorphism $D_m(F_u)\cong F_{D_m(u)}$. It commutes with the first-coordinate projections to
$D_m(P)$ and with maps commuting with $u$. Combining it for $u=1-s$ with step 5 gives a natural
chain isomorphism $D_m(\mathsf R(X))\cong\mathsf R(D_m(X))$ that retains every projection. No
infinite totalization is being interchanged with a product. Dependencies:
def-pc-tensor-complex-sheaves, def-weil-abstract-derived-category.

7. Represent $H$ by $Q\mathsf R(X)$ using step 1. Start with $A_{m,\mathsf R(X)}^{-1}$ from step
3, apply the chain isomorphism of step 6, delete the prefix by step 4 applied to the strict
tower $D_m(X_n)$, and use [lem-weil-strict-roos-comparison] on that tail. The composite is the
asserted isomorphism from $\operatorname{Res}(H\otimes_R^LB_m)$ to $R\!\lim_{n\geq h}D_m(X_n)$.
Its composite with projection to level $n$ is $D_m(p_n)$ after $A_m^{-1}$: this holds at chain
level in steps 4–6 and for the normalized derived-limit comparison in step 1. Naturality of
$A_m$ says exactly that this is the restriction of the derived tensor of $p_n$, followed by the
stated two-term comparison. Dependencies: lem-weil-strict-roos-comparison,
lem-cbc-regular-quotient-cone-augmentation.

8. For the constant tail $N$, put $P_N=\prod_{n\geq m}N$ and $u=1-s$. Define $v:P_N\to P_N$ by
$(vz)_m=0$ and $(vz)_n=-\sum_{j=m}^{n-1}z_j$ for $n>m$. These are finite sums, so define sheaf
maps and commute with $d$. One has $uv=1$ and $x=\operatorname{diag}(x_m)+vux$. Hence $P_N\cong
N\oplus P_N$ by $x\mapsto(x_m,ux)$, and $F_u\cong N\oplus F_{1_{P_N}}$ by
$(x,y)\mapsto(x_m,(ux,y))$. The second factor contracts by $(a,b)\mapsto(b,0)$. Therefore
$e:F_u\to N$, $(x,y)\mapsto x_m$, is inverse in the derived category to the diagonal $N\to F_u$,
$z\mapsto(\operatorname{diag}z,0)$. This fixes the diagonal identification required in the
statement. Dependencies: def-weil-abstract-derived-category.

9. Now put $h=m$. The augmentations $D_m(X_n)\to X_n\otimes B_m$ commute strictly with
transitions. The assumed compatibility of $f_n$ makes their composites
$g_n:D_m(X_n)\to\operatorname{Res}N$ a strict map to the constant tail. Under the normalized
comparison [lem-weil-strict-roos-comparison], their derived-limit map is exactly the
coordinatewise map of Roos fibres. Applying $e$ from step 8 selects its first product component
at $m$. Consequently the complete composite of the statement, on the model $D_m(\mathsf R(X))$,
is $$D_m(\mathsf
R(X))\xrightarrow{D_m(p_m)}D_m(X_m)\xrightarrow{\mathrm{aug}}X_m\otimes_RB_m
\xrightarrow{f_m}\operatorname{Res}N.$$
This is an equality of the indicated chain maps, not an inference that arbitrary morphisms into
a homotopy limit are determined by their projections. Dependencies:
lem-weil-strict-roos-comparison, def-pc-tensor-complex-sheaves.

10. Choose a K-flat resolution $q:P\to\mathsf R(X)$ by [lem-pc-kflat-resolution]. Ordinary
scalar extension and restriction on complexes have the specified adjunction
[def-weil-pbc-ringed-scalar-extension-complex-adjunction], with unit $p\mapsto p\otimes1$ by
[def-weil-pbc-ringed-tensor-section-calculus]. Derive it using
[lem-pc-derived-adjoint-functors], [lem-pur-derived-change-of-rings], and exact restriction
[lem-sf-exact-functor-derived-triangulated]: kernels and sheafified cokernels have unchanged
underlying abelian sheaves [def-weil-sheaf-of-modules-category]. On $P$, the map
$H\to\operatorname{Res}N$ in the statement is represented by $p\mapsto f_m(p_mq(p)\otimes1)$.
Its adjoint is represented on $P\otimes B_m$ by $p\otimes b\mapsto b f_m(p_mq(p)\otimes1)$.
After the augmentation $D_m(P)\to P\otimes B_m$ this sends $(a,b)$ to $f_m(p_mq(a)\otimes1)$,
exactly the map in step 9 precomposed with $D_m(q)$. Both $D_m(q)$ and this augmentation are
quasi-isomorphisms, by steps 2–3. The normalization of
[lem-cbc-regular-quotient-cone-augmentation] identifies this roof with $A_m^{-1}$. Thus the
equality is precisely the restriction of the derived adjoint asserted, including its unit
normalization. Dependencies: lem-pc-kflat-resolution,
def-weil-pbc-ringed-scalar-extension-complex-adjunction,
def-weil-pbc-ringed-tensor-section-calculus, lem-pc-derived-adjoint-functors,
lem-pur-derived-change-of-rings, lem-sf-exact-functor-derived-triangulated,
def-weil-sheaf-of-modules-category, lem-cbc-regular-quotient-cone-augmentation.

11. Restriction along $R\to B_m$ preserves and reflects vanishing of cohomology: it leaves the
underlying abelian sheaves unchanged and is exact, by [def-pc-sheaf-restrict-scalars] and the
kernel/cokernel description [def-weil-sheaf-of-modules-category]. It is triangulated by
[lem-sf-exact-functor-derived-triangulated]. If the restriction of a derived morphism $a:A\to B$
is invertible, its cone restricts to zero, so that cone is acyclic and hence zero in the derived
category. In the triangle $A\xrightarrow a B\to0\to A[1]$, exactness of
$\operatorname{Hom}(B,-)$ from [lem-weil-pbc-hom-into-triangle-exact] supplies $r$ with $ar=1$.
In the backward rotation $0[-1]\to A\xrightarrow a B\to0$, the same exactness with source $A$
gives $ra-1=0$ since $a(ra-1)=0$. Thus $a$ is invertible. This proves detection of isomorphisms
without asserting faithfulness or fullness of derived restriction. Dependencies:
def-pc-sheaf-restrict-scalars, def-weil-sheaf-of-modules-category,
lem-sf-exact-functor-derived-triangulated, lem-weil-pbc-hom-into-triangle-exact,
def-weil-abstract-derived-category.

12. For $k\leq m$, the map $K_m\to K_k$ has components $t^{m-k}$ in degree $-1$ and $1$ in
degree $0$. It is a chain map because $t^k t^{m-k}=t^m$, and it commutes with the augmentations
via $B_m\to B_k$. On $D_m(C)^q$ it sends $(a,b)$ to $(a,t^{m-k}b)$. On $P\otimes B_m$, for a
single K-flat resolution $P$, the corresponding map is $p\otimes\bar r\mapsto p\otimes\bar r$
modulo $t^k$. The augmentation square therefore commutes on both summands. By
[lem-pur-derived-change-of-rings] these are the coefficient quotient transitions; step 3
identifies their restrictions with the displayed $K$-maps. The permutations in steps 5–6 and
tail deletion act on independent coordinates and commute with these maps. Compare different
tails on the common tail $n\geq\max(h_m,h_k)$; the deletion maps compose literally. All
resulting derived comparison squares commute. For $j\leq k\leq m$ the degree $-1$ components
compose because $t^{k-j}t^{m-k}=t^{m-j}$; identity transitions have components $(1,1)$. If
compatible target families are also varied, the formulas of steps 9–10 give the corresponding
naturality square on the same resolution. Dependencies: def-pc-tensor-complex-sheaves,
lem-pur-derived-change-of-rings, lem-cbc-regular-quotient-cone-augmentation.

13. Finally suppose $H^q(X_n)=0$ for all $q\notin[a,b]$ and all $n$. Exact products give
$H^q(P)=\prod_nH^q(X_n)$ as in step 1, so $P=\prod X_n$ has the same cohomological bound. In the
Roos triangle $H\to P\xrightarrow{1-s}P\to H[1]$, use [lem-sf-derived-homology-long-exact]: the
segment $H^{q-1}(P)\to H^q(H)\to H^q(P)$ has both outside terms zero for $q<a$ or $q>b+1$. Thus
$H^q(H)=0$ there, proving the interval $[a,b+1]$. The product exactness statement used here
holds for every scheme, and none of the coordinate calculations imposed quasi-compactness on
$T$. Dependencies: lem-weil-proetale-countable-products-exact, lem-weil-strict-roos-comparison,
lem-sf-derived-homology-long-exact.
-/
theorem koszulRoosProjectionComparison (T : AlgebraicGeometry.Scheme.{t})
    [EssentiallySmall.{t + 1} T.ProEt]
    (R : Sheaf (AlgebraicGeometry.Scheme.ProEt.topology T) CommRingCat.{max z (t + 1)})
    (s : (R.obj ⋙ forget CommRingCat.{max z (t + 1)}).sections)
    [∀ S : Sheaf (AlgebraicGeometry.Scheme.ProEt.topology T) CommRingCat.{max z (t + 1)},
      HasDerivedCategory.{w} (Modules S)]
    [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ Modules R)]
    (_hs : Mono (globalSectionMultiplication R (unitSection R s))) :
    Conclusion R s := by
  obtain ⟨i, h⟩ := normalizedKoszulRoosModels T R s _hs
  let := i
  obtain ⟨M, hM⟩ := h
  exact ⟨i, M, compatibility_of_normalization R s M hM
    (koszulRoosCoefficientCompatibility R s M hM)⟩

end CategoryTheory.KoszulRoos
