/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q104
-/
module

public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.ShortExact
public import Mathlib.Algebra.Homology.HomotopyCategory.SingleFunctors
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Sheaf.CategoryTheory.CochainCoefficientUniverseTransport

/-! # The natural augmentation fiber of an exact four-term row

Source: the current blueprint, `sk-lem-sp-tower`, first proof paragraph; Stacks Tags
014E (cone), 011G (shift), and 0115 (quasi-isomorphism)
(blueprint: lem-sp-exact-row-augmentation-fiber).

The auxiliary constructions use Mathlib's single complexes and mapping cones. The
coordinate projections remove their zero summands, so their signs are fixed canonically.
- Even before imposing exactness, `augmentation` and `fiberMap` are actual chain maps.
- `exactRowAugmentationFiber` states the coordinates, quasi-isomorphism and naturality.
-/

@[expose] public section

set_option autoImplicit false

universe uA vA uC vC r w s

open CategoryTheory CategoryTheory.Limits SheafOfModules.CochainUniverseTransport

namespace CochainComplex.ExactRowAugmentation

variable {𝒜 : Type uA} [Category.{vA} 𝒜] [Abelian 𝒜]
    {B C D : 𝒜} (d : B ⟶ C) (q : C ⟶ D) (hdq : d ≫ q = 0)

/-- The degree-zero short complex whose first cone is `[B → C]` in degrees `-1,0`.
Source: Stacks Tag 014E (blueprint: lem-sp-exact-row-augmentation-fiber). -/
noncomputable def singles : ShortComplex (CochainComplex 𝒜 ℤ) :=
  ShortComplex.mk ((singleFunctor 𝒜 0).map d)
    ((singleFunctor 𝒜 0).map q) (by
      rw [← Functor.map_comp, hdq, Functor.map_zero])

/-- The augmentation with coordinate `q` in degree zero and zero on the other summand.
Source: Stacks Tag 014E (blueprint: lem-sp-exact-row-augmentation-fiber). -/
noncomputable def augmentation :
    mappingCone ((singleFunctor 𝒜 0).map d) ⟶
      (singleFunctor 𝒜 0).obj D :=
  mappingCone.descShortComplex (singles d q hdq)

/-- The specified mapping fiber, with Mathlib's cone and shift conventions.
Source: Stacks Tags 014E and 011G (blueprint: lem-sp-exact-row-augmentation-fiber). -/
noncomputable def fiber : CochainComplex 𝒜 ℤ :=
  (mappingCone (augmentation d q hdq))⟦(-1 : ℤ)⟧

/-- The canonical degree `-1` coordinate of the shifted cone, obtained by its projections.
Source: Stacks Tags 014E and 011G (blueprint: lem-sp-exact-row-augmentation-fiber). -/
noncomputable def toB : (fiber d q hdq).X (-1) ⟶ B :=
  HomologicalComplex.homotopyCofiber.fstX (augmentation d q hdq) (-2) (-1) (by decide) ≫
    HomologicalComplex.homotopyCofiber.fstX
      ((singleFunctor 𝒜 0).map d) (-1) 0 (by decide) ≫
    (HomologicalComplex.singleObjXSelf (.up ℤ) 0 B).hom

/-- The canonical degree-zero coordinate of the shifted cone.
Source: Stacks Tags 014E and 011G (blueprint: lem-sp-exact-row-augmentation-fiber). -/
noncomputable def toC : (fiber d q hdq).X 0 ⟶ C :=
  HomologicalComplex.homotopyCofiber.fstX (augmentation d q hdq) (-1) 0 (by decide) ≫
    HomologicalComplex.homotopyCofiber.sndX ((singleFunctor 𝒜 0).map d) 0 ≫
    (HomologicalComplex.singleObjXSelf (.up ℤ) 0 C).hom

/-- The canonical degree-one coordinate of the shifted cone.
Source: Stacks Tags 014E and 011G (blueprint: lem-sp-exact-row-augmentation-fiber). -/
noncomputable def toD : (fiber d q hdq).X 1 ⟶ D :=
  HomologicalComplex.homotopyCofiber.sndX (augmentation d q hdq) 0 ≫
    (HomologicalComplex.singleObjXSelf (.up ℤ) 0 D).hom

private lemma fst_isIso {K L : CochainComplex 𝒜 ℤ} (f : K ⟶ L)
    (n m : ℤ) (h : n + 1 = m) (hz : IsZero (L.X n)) :
    IsIso (HomologicalComplex.homotopyCofiber.fstX f n m h) := by
  refine ⟨⟨HomologicalComplex.homotopyCofiber.inlX f m n h, ?_, ?_⟩⟩
  · apply HomologicalComplex.homotopyCofiber.ext_to_X f n m h
    · simp
    · exact hz.eq_of_tgt _ _
  · simp

private lemma snd_isIso {K L : CochainComplex 𝒜 ℤ} (f : K ⟶ L)
    (n m : ℤ) (h : n + 1 = m) (hz : IsZero (K.X m)) :
    IsIso (HomologicalComplex.homotopyCofiber.sndX f n) := by
  refine ⟨⟨HomologicalComplex.homotopyCofiber.inrX f n, ?_, ?_⟩⟩
  · apply HomologicalComplex.homotopyCofiber.ext_to_X f n m h
    · exact hz.eq_of_tgt _ _
    · simp
  · simp

private lemma coordinates :
    IsIso (toB d q hdq) ∧ IsIso (toC d q hdq) ∧ IsIso (toD d q hdq) := by
  have hz (X : 𝒜) (n : ℤ) (hn : n ≠ 0) :
      IsZero (((singleFunctor 𝒜 0).obj X).X n) :=
    HomologicalComplex.isZero_single_obj_X _ _ _ _ hn
  have h₁ := fst_isIso (augmentation d q hdq) (-2) (-1) (by decide) (hz D _ (by decide))
  have h₂ := fst_isIso ((singleFunctor 𝒜 0).map d) (-1) 0 (by decide)
    (hz C _ (by decide))
  have h₃ := fst_isIso (augmentation d q hdq) (-1) 0 (by decide) (hz D _ (by decide))
  have h₄ := snd_isIso ((singleFunctor 𝒜 0).map d) 0 1 (by decide) (hz B _ (by decide))
  have h₅ := snd_isIso (augmentation d q hdq) 0 1 (by decide) (by
    rw [mappingCone.isZero_X_iff]
    exact ⟨hz B _ (by decide), hz C _ (by decide)⟩)
  dsimp only [toB, toC, toD]
  exact ⟨inferInstance, inferInstance, inferInstance⟩

private lemma support (n : ℤ) (h₁ : n ≠ -1) (h₀ : n ≠ 0) (h₂ : n ≠ 1) :
    IsZero ((fiber d q hdq).X n) := by
  change IsZero ((mappingCone (augmentation d q hdq)).X (n + -1))
  rw [mappingCone.isZero_X_iff, mappingCone.isZero_X_iff]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  all_goals apply HomologicalComplex.isZero_single_obj_X
  all_goals omega

private lemma differentialB :
    (fiber d q hdq).d (-1) 0 ≫ toC d q hdq = toB d q hdq ≫ d := by
  dsimp only [fiber]
  rw [shiftFunctor_obj_d']
  simp only [Int.reduceNeg, Int.reduceAdd, Int.negOnePow_neg, Int.negOnePow_one,
    Units.neg_smul, one_smul, Preadditive.neg_comp]
  change -(mappingCone (augmentation d q hdq)).d (-2) (-1) ≫
    toC d q hdq = toB d q hdq ≫ d
  dsimp only [toC, toB]
  erw [← Category.assoc, ← Category.assoc,
    show (mappingCone (augmentation d q hdq)).d (-2) (-1) ≫
      HomologicalComplex.homotopyCofiber.fstX (augmentation d q hdq) (-1) 0 (by decide) =
      -HomologicalComplex.homotopyCofiber.fstX (augmentation d q hdq) (-2) (-1)
        (by decide) ≫ (mappingCone ((singleFunctor 𝒜 0).map d)).d (-1) 0 from by
      simpa only [mappingCone, HomologicalComplex.homotopyCofiber_d] using
        HomologicalComplex.homotopyCofiber.d_fstX (augmentation d q hdq)
          (-2) (-1) 0 (by decide) (by decide), Preadditive.neg_comp,
    Preadditive.neg_comp, neg_neg]
  simp only [Category.assoc]
  erw [← Category.assoc _ _ (HomologicalComplex.singleObjXSelf _ 0 C).hom,
    show (mappingCone ((singleFunctor 𝒜 0).map d)).d (-1) 0 ≫
      HomologicalComplex.homotopyCofiber.sndX ((singleFunctor 𝒜 0).map d) 0 =
      _ from by
        simpa only [mappingCone, HomologicalComplex.homotopyCofiber_d] using
          HomologicalComplex.homotopyCofiber.d_sndX
            ((singleFunctor 𝒜 0).map d) (-1) 0 (by decide)]
  dsimp only [singleFunctor, singleFunctors]
  simp [HomologicalComplex.single_map_f_self, Category.assoc]

private lemma differentialC :
    (fiber d q hdq).d 0 1 ≫ toD d q hdq = -(toC d q hdq ≫ q) := by
  dsimp only [fiber]
  rw [shiftFunctor_obj_d']
  simp only [Int.reduceNeg, Int.reduceAdd, Int.negOnePow_neg, Int.negOnePow_one,
    Units.neg_smul, one_smul, Preadditive.neg_comp]
  change -(mappingCone (augmentation d q hdq)).d (-1) 0 ≫
    toD d q hdq = -(toC d q hdq ≫ q)
  dsimp only [toD, toC]
  erw [← Category.assoc, show
    (mappingCone (augmentation d q hdq)).d (-1) 0 ≫
      HomologicalComplex.homotopyCofiber.sndX (augmentation d q hdq) 0 =
      _ from by
        simpa only [mappingCone, HomologicalComplex.homotopyCofiber_d] using
          HomologicalComplex.homotopyCofiber.d_sndX
            (augmentation d q hdq) (-1) 0 (by decide)]
  simp only [singleFunctor_obj_d, comp_zero, add_zero]
  congr 1
  dsimp only [augmentation, mappingCone.descShortComplex]
  rw [mappingCone.desc_f _ _ _ _ 0 1 (by decide)]
  dsimp only [singleFunctor, singleFunctors, singles]
  simp [mappingCone.snd, HomologicalComplex.single_map_f_self, Category.assoc]

private lemma singleShift_zero (X : 𝒜) (n : ℤ) (hn : n ≠ -1) :
    IsZero ((((singleFunctor 𝒜 0).obj X)⟦(1 : ℤ)⟧).X n) := by
  change IsZero (((singleFunctor 𝒜 0).obj X).X (n + 1))
  apply HomologicalComplex.isZero_single_obj_X
  omega

private noncomputable def inclusion {A : 𝒜} (a : A ⟶ B) (had : a ≫ d = 0) :
    ((singleFunctor 𝒜 0).obj A)⟦(1 : ℤ)⟧ ⟶ fiber d q hdq := by
  letI := (coordinates d q hdq).1
  letI := (coordinates d q hdq).2.1
  let f : (((singleFunctor 𝒜 0).obj A)⟦(1 : ℤ)⟧).X (-1) ⟶
      (fiber d q hdq).X (-1) :=
    (HomologicalComplex.singleObjXSelf (.up ℤ) 0 A).hom ≫ a ≫ inv (toB d q hdq)
  exact
    { f := fun n ↦ if h : n = -1 then
        eqToHom (congrArg (fun k ↦ (((singleFunctor 𝒜 0).obj A)⟦(1 : ℤ)⟧).X k) h) ≫
          f ≫ eqToHom (congrArg (fun k ↦ (fiber d q hdq).X k) h.symm) else 0
      comm' := by
        intro n m hnm
        by_cases hn : n = -1
        · subst n
          have hm : m = 0 := by simpa using hnm.symm
          subst m
          simp only [↓reduceDIte, eqToHom_refl, Category.id_comp, Category.comp_id, Int.reduceAdd]
          have hz : (((singleFunctor 𝒜 0).obj A)⟦(1 : ℤ)⟧).d (-1) 0 = 0 := by
            rw [shiftFunctor_obj_d']; simp
          rw [hz, zero_comp]
          apply (cancel_mono (toC d q hdq)).mp
          simp [f, Category.assoc, differentialB, had]
        · exact (singleShift_zero A n hn).eq_of_src _ _ }

private lemma inclusion_f {A : 𝒜} (a : A ⟶ B) (had : a ≫ d = 0) :
    (inclusion d q hdq a had).f (-1) ≫ toB d q hdq =
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 A).hom ≫ a := by
  let := (coordinates d q hdq).1
  simp [inclusion, Category.assoc]

private lemma inclusion_zero {A : 𝒜} (a : A ⟶ B) (had : a ≫ d = 0)
    (n : ℤ) (hn : n ≠ -1) : (inclusion d q hdq a had).f n = 0 :=
  (singleShift_zero A n hn).eq_of_src _ _

private lemma inclusion_quasiIso {A : 𝒜} (a : A ⟶ B) (had : a ≫ d = 0)
    [Mono a] [Epi q] (hexB : (ShortComplex.mk a d had).Exact)
    (hexC : (ShortComplex.mk d q hdq).Exact) : QuasiIso (inclusion d q hdq a had) := by
  obtain ⟨hB, hC, hD⟩ := coordinates d q hdq
  let := hB
  let := hC
  let := hD
  let F := fiber d q hdq
  let i := inclusion d q hdq a had
  have hi : i.f (-1) ≫ toB d q hdq =
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 A).hom ≫ a := inclusion_f d q hdq a had
  have hker : IsLimit (KernelFork.ofι (a ≫ inv (toB d q hdq))
      (show (a ≫ inv (toB d q hdq)) ≫ F.d (-1) 0 = 0 by
        apply (cancel_mono (toC d q hdq)).mp
        simp [F, Category.assoc, differentialB, had])) := by
    apply KernelFork.isLimitOfIsLimitOfIff hexB.fIsKernel (F.d (-1) 0)
      (asIso (toB d q hdq)).symm
    intro W t
    rw [← cancel_mono (toC d q hdq)]
    simp [F, Category.assoc, differentialB]
  rw [quasiIso_iff]
  intro n
  by_cases hn : n = -1
  · subst n
    rw [quasiIsoAt_iff' _ (-2) (-1) 0 (by simp) (by simp)]
    let T := F.sc' (-2) (-1) 0
    let U := (((singleFunctor 𝒜 0).obj A)⟦(1 : ℤ)⟧).sc' (-2) (-1) 0
    let ψ : U ⟶ T :=
      (HomologicalComplex.shortComplexFunctor' 𝒜 (.up ℤ) (-2) (-1) 0).map i
    have hf : T.f = 0 := (support d q hdq (-2) (by decide) (by decide)
      (by decide)).eq_of_src _ _
    have hfU : U.f = 0 := (singleShift_zero A (-2) (by decide)).eq_of_src _ _
    have hgU : U.g = 0 := (singleShift_zero A 0 (by decide)).eq_of_tgt _ _
    let H₁ := ShortComplex.LeftHomologyData.ofZeros U hfU hgU
    let H₂ := ShortComplex.LeftHomologyData.ofIsLimitKernelFork T hf _ hker
    let μ : ShortComplex.LeftHomologyMapData ψ H₁ H₂ :=
      { φK := (HomologicalComplex.singleObjXSelf (.up ℤ) 0 A).hom
        φH := (HomologicalComplex.singleObjXSelf (.up ℤ) 0 A).hom
        commi := by
          change _ ≫ (a ≫ inv (toB d q hdq)) = 𝟙 _ ≫ i.f (-1)
          apply (cancel_mono (toB d q hdq)).mp
          simpa [Category.assoc] using hi.symm
        commπ := by change 𝟙 _ ≫ _ = _ ≫ 𝟙 _; simp }
    exact μ.quasiIso_iff.mpr (by dsimp [μ]; infer_instance)
  · rw [quasiIsoAt_iff_exactAt _ n
      (HomologicalComplex.ExactAt.of_isZero (singleShift_zero A n hn))]
    by_cases hn₀ : n = 0
    · subst n
      rw [F.exactAt_iff' (i := -1) (j := 0) (k := 1) (by simp) (by simp)]
      let ψ : F.sc' (-1) 0 1 ⟶ ShortComplex.mk d q hdq :=
        { τ₁ := toB d q hdq
          τ₂ := toC d q hdq
          τ₃ := -(toD d q hdq)
          comm₁₂ := (differentialB d q hdq).symm
          comm₂₃ := by
            change toC d q hdq ≫ q = F.d 0 1 ≫ (-(toD d q hdq))
            simp [F, Preadditive.comp_neg, differentialC] }
      exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono ψ).mpr hexC
    · by_cases hn₁ : n = 1
      · subst n
        rw [F.exactAt_iff' (i := 0) (j := 1) (k := 2) (by simp) (by simp)]
        apply (ShortComplex.exact_iff_epi _
          ((support d q hdq 2 (by decide) (by decide) (by decide)).eq_of_tgt _ _)).mpr
        have h : Epi (F.d 0 1 ≫ toD d q hdq) := by
          rw [show F.d 0 1 ≫ toD d q hdq = -(toC d q hdq ≫ q) from
            differentialC d q hdq]
          infer_instance
        exact (epi_comp_iff_of_isIso _ (toD d q hdq)).mp h
      · exact HomologicalComplex.ExactAt.of_isZero (support d q hdq n hn hn₀ hn₁)

variable {B' C' D' : 𝒜} (d' : B' ⟶ C') (q' : C' ⟶ D')
    (hdq' : d' ≫ q' = 0) (β : B' ⟶ B) (γ : C' ⟶ C) (δ : D' ⟶ D)
    (hβγ : d' ≫ γ = β ≫ d) (hγδ : q' ≫ δ = γ ≫ q)

/-- The map of two-term complexes induced by the middle square.
Source: Stacks Tag 014E (blueprint: lem-sp-exact-row-augmentation-fiber). -/
noncomputable def twoTermMap :=
  mappingCone.map ((singleFunctor 𝒜 0).map d')
    ((singleFunctor 𝒜 0).map d)
    ((singleFunctor 𝒜 0).map β) ((singleFunctor 𝒜 0).map γ)
    (by rw [← Functor.map_comp, ← Functor.map_comp, hβγ])

/-- The strict shifted cone map induced by the square of augmentations.
Source: Stacks Tags 014E and 011G (blueprint: lem-sp-exact-row-augmentation-fiber).
The augmentation square is the existing `map_descShortComplex` identity applied to
its three degree-zero maps, and its cone map has no homotopy correction term. -/
noncomputable def fiberMap : fiber d' q' hdq' ⟶ fiber d q hdq :=
  (CategoryTheory.shiftFunctor (CochainComplex 𝒜 ℤ) (-1 : ℤ)).map
    (mappingCone.map (augmentation d' q' hdq') (augmentation d q hdq)
      (twoTermMap d d' β γ hβγ) ((singleFunctor 𝒜 0).map δ)
      (mappingCone.map_descShortComplex (singles d' q' hdq') (singles d q hdq)
        { τ₁ := (singleFunctor 𝒜 0).map β
          τ₂ := (singleFunctor 𝒜 0).map γ
          τ₃ := (singleFunctor 𝒜 0).map δ
          comm₁₂ := by dsimp [singles]; rw [← Functor.map_comp, ← Functor.map_comp, hβγ]
          comm₂₃ := by dsimp [singles]; rw [← Functor.map_comp, ← Functor.map_comp, hγδ] }).symm)

private lemma coneMap_fst {K L K' L' : CochainComplex 𝒜 ℤ}
    (f : K ⟶ L) (g : K' ⟶ L') (a : K ⟶ K') (b : L ⟶ L')
    (h : f ≫ b = a ≫ g) (n m : ℤ) (hnm : n + 1 = m) :
    (mappingCone.map f g a b h).f n ≫
      HomologicalComplex.homotopyCofiber.fstX g n m hnm =
      HomologicalComplex.homotopyCofiber.fstX f n m hnm ≫ a.f m := by
  change (mappingCone.map f g a b h).f n ≫ (mappingCone.fst g).1.v n m hnm =
    (mappingCone.fst f).1.v n m hnm ≫ a.f m
  apply mappingCone.ext_from f m n hnm
  all_goals simp [mappingCone.map]

private lemma coneMap_snd {K L K' L' : CochainComplex 𝒜 ℤ}
    (f : K ⟶ L) (g : K' ⟶ L') (a : K ⟶ K') (b : L ⟶ L')
    (h : f ≫ b = a ≫ g) (n : ℤ) :
    (mappingCone.map f g a b h).f n ≫
      HomologicalComplex.homotopyCofiber.sndX g n =
      HomologicalComplex.homotopyCofiber.sndX f n ≫ b.f n := by
  have aux : (mappingCone.map f g a b h).f n ≫
      (mappingCone.snd g).v n n (add_zero n) =
      (mappingCone.snd f).v n n (add_zero n) ≫ b.f n := by
    apply mappingCone.ext_from f (n + 1) n rfl
    all_goals simp [mappingCone.map]
  simpa [mappingCone.snd] using aux

private lemma map_coordinates :
    (fiberMap d q hdq d' q' hdq' β γ δ hβγ hγδ).f (-1) ≫ toB d q hdq =
      toB d' q' hdq' ≫ β ∧
    (fiberMap d q hdq d' q' hdq' β γ δ hβγ hγδ).f 0 ≫ toC d q hdq =
      toC d' q' hdq' ≫ γ ∧
    (fiberMap d q hdq d' q' hdq' β γ δ hβγ hγδ).f 1 ≫ toD d q hdq =
      toD d' q' hdq' ≫ δ := by
  dsimp only [fiberMap]
  simp only [shiftFunctor_map_f', Int.reduceAdd, Int.reduceNeg]
  refine ⟨?_, ?_, ?_⟩
  · dsimp only [toB]
    rw [← Category.assoc, coneMap_fst, Category.assoc]
    dsimp only [twoTermMap]
    simp only [Category.assoc]
    erw [← Category.assoc _ _ (HomologicalComplex.singleObjXSelf _ 0 B).hom,
      coneMap_fst]
    dsimp only [singleFunctor, singleFunctors]
    simp [HomologicalComplex.single_map_f_self, Category.assoc]
  · dsimp only [toC]
    rw [← Category.assoc, coneMap_fst, Category.assoc]
    dsimp only [twoTermMap]
    simp only [Category.assoc]
    erw [← Category.assoc _ _ (HomologicalComplex.singleObjXSelf _ 0 C).hom,
      coneMap_snd]
    dsimp only [singleFunctor, singleFunctors]
    simp [HomologicalComplex.single_map_f_self, Category.assoc]
  · dsimp only [toD]
    simp only [Category.assoc]
    erw [← Category.assoc _ _ (HomologicalComplex.singleObjXSelf _ 0 D).hom,
      coneMap_snd]
    dsimp only [singleFunctor, singleFunctors]
    simp [HomologicalComplex.single_map_f_self, Category.assoc]

private lemma inclusion_naturality {A A' : 𝒜} (a : A ⟶ B) (a' : A' ⟶ B')
    (had : a ≫ d = 0) (had' : a' ≫ d' = 0) (α : A' ⟶ A)
    (hαβ : a' ≫ β = α ≫ a) :
    inclusion d' q' hdq' a' had' ≫ fiberMap d q hdq d' q' hdq' β γ δ hβγ hγδ =
      ((singleFunctor 𝒜 0).map α)⟦(1 : ℤ)⟧' ≫ inclusion d q hdq a had := by
  let := (coordinates d q hdq).1
  ext n
  by_cases hn : n = -1
  · subst n
    apply (cancel_mono (toB d q hdq)).mp
    simp only [HomologicalComplex.comp_f, Category.assoc]
    rw [(map_coordinates d q hdq d' q' hdq' β γ δ hβγ hγδ).1, inclusion_f]
    rw [← Category.assoc, inclusion_f]
    simp only [Category.assoc, hαβ, shiftFunctor_map_f']
    change _ = ((singleFunctor 𝒜 0).map α).f 0 ≫ _
    dsimp only [singleFunctor, singleFunctors]
    simp [HomologicalComplex.single_map_f_self, Category.assoc]
  · exact (singleShift_zero A' n hn).eq_of_src _ _

end CochainComplex.ExactRowAugmentation

namespace CochainComplex.ExactRowAugmentation

variable {𝒞 : Type uC} [Category.{vC} 𝒞] {J : GrothendieckTopology 𝒞}
    (S : Sheaf J CommRingCat.{s})

/-- The shifted augmentation fiber of an exact four-term row, with its specified natural
quasi-isomorphism and derived isomorphism.

Source: current blueprint `sk-lem-sp-tower`, first proof paragraph, expanded using Stacks
Tags 014E, 011G and 0115 (blueprint: lem-sp-exact-row-augmentation-fiber).

Proof: (1) The two composites vanish by exactness. In `Cone(ε)` the nonzero terms are
B,C,D in degrees -2,-1,0 and the differentials are -d,q. Shifting by -1 negates them,
so the canonical zero-summand projections give B,C,D in degrees -1,0,1 with d,-q.
(2) The coordinate a defines a chain map because a ≫ d = 0. Its only nonzero cohomology
map is A → ker d, an isomorphism by monicity of a and exactness at B. Exactness at C
and epimorphicity of q kill the remaining cohomology. Thus it is a quasi-isomorphism,
and localization gives the displayed isomorphism with precisely its image as hom.
(3) For a second row, the commuting middle square gives `twoTermMap`; the final square
makes the augmentations commute by `map_descShortComplex`. The strict cone map is
block diagonal, hence after shifting its coordinates are β,γ,δ. (4) The two composites
out of A'[1] agree in degree -1 by a' ≫ β = α ≫ a, and elsewhere because the source
is zero. Applying Q gives the naturality identity of the specified isomorphisms.
These steps use def-weil-sheaf-of-modules-category and def-weil-abstract-derived-category.
The coordinate condition uniquely determines each inclusion, so the existential
comparisons are the specified canonical ones, simultaneously for every row diagram. -/
theorem exactRowAugmentationFiber
    [HasDerivedCategory.{w} (OriginalModules.{uC, vC, s, max uC vC r} S)]
    {A B C D : OriginalModules.{uC, vC, s, max uC vC r} S} (a : A ⟶ B) (d : B ⟶ C) (q : C ⟶ D)
    (had : a ≫ d = 0) (hdq : d ≫ q = 0) [Mono a] [Epi q]
    (hexB : (ShortComplex.mk a d had).Exact)
    (hexC : (ShortComplex.mk d q hdq).Exact) :
    IsIso (toB d q hdq) ∧ IsIso (toC d q hdq) ∧ IsIso (toD d q hdq) ∧
    (∀ n : ℤ, n ≠ -1 → n ≠ 0 → n ≠ 1 → IsZero ((fiber d q hdq).X n)) ∧
    (fiber d q hdq).d (-1) 0 ≫ toC d q hdq = toB d q hdq ≫ d ∧
    (fiber d q hdq).d 0 1 ≫ toD d q hdq = -(toC d q hdq ≫ q) ∧
    ∃ (i : ((singleFunctor (OriginalModules.{uC, vC, s, max uC vC r} S) 0).obj A)⟦(1 : ℤ)⟧ ⟶
        fiber d q hdq)
      (e : DerivedCategory.Q.obj
        (((singleFunctor (OriginalModules.{uC, vC, s, max uC vC r} S) 0).obj A)⟦(1 : ℤ)⟧) ≅
        DerivedCategory.Q.obj (fiber d q hdq)),
      i.f (-1) ≫ toB d q hdq =
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 A).hom ≫ a ∧
      (∀ n : ℤ, n ≠ -1 → i.f n = 0) ∧ QuasiIso i ∧
      e.hom = DerivedCategory.Q.map i ∧
      ∀ (A' B' C' D' : OriginalModules.{uC, vC, s, max uC vC r} S)
        (a' : A' ⟶ B') (d' : B' ⟶ C') (q' : C' ⟶ D')
        (had' : a' ≫ d' = 0) (hdq' : d' ≫ q' = 0),
        Mono a' → Epi q' → (ShortComplex.mk a' d' had').Exact →
        (ShortComplex.mk d' q' hdq').Exact →
        ∃ (i' :
            ((singleFunctor (OriginalModules.{uC, vC, s, max uC vC r} S) 0).obj A')⟦(1 : ℤ)⟧ ⟶
              fiber d' q' hdq')
          (e' : DerivedCategory.Q.obj
            (((singleFunctor (OriginalModules.{uC, vC, s, max uC vC r} S) 0).obj A')⟦(1 : ℤ)⟧) ≅
            DerivedCategory.Q.obj (fiber d' q' hdq')),
          i'.f (-1) ≫ toB d' q' hdq' =
            (HomologicalComplex.singleObjXSelf (.up ℤ) 0 A').hom ≫ a' ∧
          (∀ n : ℤ, n ≠ -1 → i'.f n = 0) ∧ QuasiIso i' ∧
          e'.hom = DerivedCategory.Q.map i' ∧
          ∀ (α : A' ⟶ A) (β : B' ⟶ B) (γ : C' ⟶ C) (δ : D' ⟶ D)
            (_hαβ : a' ≫ β = α ≫ a) (hβγ : d' ≫ γ = β ≫ d)
            (hγδ : q' ≫ δ = γ ≫ q),
            (fiberMap d q hdq d' q' hdq' β γ δ hβγ hγδ).f (-1) ≫ toB d q hdq =
              toB d' q' hdq' ≫ β ∧
            (fiberMap d q hdq d' q' hdq' β γ δ hβγ hγδ).f 0 ≫ toC d q hdq =
              toC d' q' hdq' ≫ γ ∧
            (fiberMap d q hdq d' q' hdq' β γ δ hβγ hγδ).f 1 ≫ toD d q hdq =
              toD d' q' hdq' ≫ δ ∧
            i' ≫ fiberMap d q hdq d' q' hdq' β γ δ hβγ hγδ =
              ((singleFunctor (OriginalModules.{uC, vC, s, max uC vC r} S) 0).map α)⟦(1 : ℤ)⟧' ≫ i ∧
            e'.hom ≫ DerivedCategory.Q.map (fiberMap d q hdq d' q' hdq' β γ δ hβγ hγδ) =
              DerivedCategory.Q.map
                (((singleFunctor (OriginalModules.{uC, vC, s, max uC vC r} S) 0).map α)⟦(1 : ℤ)⟧') ≫
                e.hom := by
  obtain ⟨hB, hC, hD⟩ := coordinates d q hdq
  refine ⟨hB, hC, hD, support d q hdq, differentialB d q hdq,
    differentialC d q hdq, ?_⟩
  let i := inclusion d q hdq a had
  let : QuasiIso i := inclusion_quasiIso d q hdq a had hexB hexC
  refine ⟨i, asIso (DerivedCategory.Q.map i), inclusion_f d q hdq a had,
    inclusion_zero d q hdq a had, inferInstance, rfl, ?_⟩
  intro A' B' C' D' a' d' q' had' hdq' hmono hepi hexB' hexC'
  let := hmono
  let := hepi
  let i' := inclusion d' q' hdq' a' had'
  let : QuasiIso i' := inclusion_quasiIso d' q' hdq' a' had' hexB' hexC'
  refine ⟨i', asIso (DerivedCategory.Q.map i'), inclusion_f d' q' hdq' a' had',
    inclusion_zero d' q' hdq' a' had', inferInstance, rfl, ?_⟩
  intro α β γ δ hαβ hβγ hγδ
  obtain ⟨hβ, hγ, hδ⟩ := map_coordinates d q hdq d' q' hdq' β γ δ hβγ hγδ
  have hnat := inclusion_naturality d q hdq d' q' hdq' β γ δ hβγ hγδ
    a a' had had' α hαβ
  refine ⟨hβ, hγ, hδ, hnat, ?_⟩
  simpa only [Functor.map_comp, asIso_hom, i, i'] using
    congrArg DerivedCategory.Q.map hnat

end CochainComplex.ExactRowAugmentation
