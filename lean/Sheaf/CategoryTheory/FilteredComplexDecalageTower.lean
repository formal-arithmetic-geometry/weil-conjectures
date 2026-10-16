/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G4
-/
module

public import Sheaf.CategoryTheory.FilteredComplexDecalage
public import Mathlib.Algebra.Homology.HomotopyCategory.SpectralObject
public import WeilConjectures.Mathlib.CategoryTheory.Triangulated.SpectralObject
public import Mathlib.Order.WithBotTop
public import Mathlib.Algebra.Homology.HomotopyCategory.ShortExact

/-! # The tower of decalage steps

Source: Stacks Project, Tags 015X and 012K.
(blueprint: def-sp-filtered-complex-decalage-tower).
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.DecreasingFiltration

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {K : CochainComplex C ℤ}

/-- Extend the increasing tower of decalage steps by zero and the whole complex.
Source: Stacks Project, Tag 015X (blueprint: def-sp-filtered-complex-decalage-tower). -/
noncomputable def decalageTowerStep (F : DecreasingFiltration K) : EInt → Subobject K :=
  WithBotTop.rec ⊥ (fun q ↦ F.decalage.step (1 - q)) ⊤

theorem decalageTowerStep_monotone (F : DecreasingFiltration K) :
    Monotone F.decalageTowerStep := by
  intro a b hab
  induction a using WithBotTop.rec with
  | bot => exact bot_le
  | coe a =>
    induction b using WithBotTop.rec with
    | bot => simp at hab
    | coe b =>
      apply F.decalage.antitone_step
      have : a ≤ b := by simpa using hab
      omega
    | top => exact le_top
  | top =>
    have hb : b = ⊤ := top_le_iff.mp hab
    subst b
    exact le_rfl

/-- The actual functor of subcomplexes in the decalage tower.
Source: Stacks Project, Tag 015X (blueprint: def-sp-filtered-complex-decalage-tower). -/
noncomputable def decalageTower (F : DecreasingFiltration K) :
    EInt ⥤ CochainComplex C ℤ where
  obj a := (F.decalageTowerStep a : CochainComplex C ℤ)
  map f := Subobject.ofLE _ _ (F.decalageTowerStep_monotone (leOfHom f))
  map_id _ := Subobject.ofLE_refl _
  map_comp _ _ := (Subobject.ofLE_comp_ofLE ..).symm

/-- The tower has its specified inclusion into the constant total complex. -/
noncomputable def decalageTowerι (F : DecreasingFiltration K) :
    F.decalageTower ⟶ (Functor.const EInt).obj K where
  app a := (F.decalageTowerStep a).arrow
  naturality _ _ _ := by
    dsimp [decalageTower]
    simp only [Subobject.ofLE_arrow, Category.comp_id]

end CategoryTheory.DecreasingFiltration

namespace CategoryTheory.DecreasingFiltration

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- A filtered map preserves the extended tower, including its endpoints. -/
theorem decalageTowerStep_preserves
    {U V : FilteredObject (CochainComplex C ℤ)} (t : U ⟶ V) (a : EInt) :
    ∃ k : (U.filtration.decalageTowerStep a : CochainComplex C ℤ) ⟶
      (V.filtration.decalageTowerStep a : CochainComplex C ℤ),
      k ≫ (V.filtration.decalageTowerStep a).arrow =
        (U.filtration.decalageTowerStep a).arrow ≫ t.hom := by
  induction a using WithBotTop.rec with
  | bot =>
    refine ⟨0, ?_⟩
    simp [decalageTowerStep]
  | coe a => exact decalage_map_preserves t (1 - a)
  | top =>
    refine ⟨(⊤ : Subobject U.obj).arrow ≫ t.hom ≫
      inv (⊤ : Subobject V.obj).arrow, ?_⟩
    dsimp [decalageTowerStep]
    simp

/-- Restrict a filtered map to its decalage tower. The monic inclusions fix every component. -/
noncomputable def decalageTowerMap
    {U V : FilteredObject (CochainComplex C ℤ)} (t : U ⟶ V) :
    U.filtration.decalageTower ⟶ V.filtration.decalageTower where
  app a := (decalageTowerStep_preserves t a).choose
  naturality a b f := by
    apply (cancel_mono (V.filtration.decalageTowerStep b).arrow).1
    rw [Category.assoc, (decalageTowerStep_preserves t b).choose_spec]
    dsimp only [decalageTower]
    rw [← Category.assoc, Subobject.ofLE_arrow, Category.assoc,
      Subobject.ofLE_arrow]
    exact (decalageTowerStep_preserves t a).choose_spec.symm

@[reassoc]
theorem decalageTowerMap_app_arrow
    {U V : FilteredObject (CochainComplex C ℤ)} (t : U ⟶ V) (a : EInt) :
    (decalageTowerMap t).app a ≫ (V.filtration.decalageTowerStep a).arrow =
      (U.filtration.decalageTowerStep a).arrow ≫ t.hom :=
  (decalageTowerStep_preserves t a).choose_spec

/-- Restriction of a filtered map to one decalage step.
The inclusion equation fixes the map uniquely. -/
noncomputable def decalageStepMap
    {U V : FilteredObject (CochainComplex C ℤ)} (t : U ⟶ V) (a : ℤ) :
    (U.filtration.decalage.step a : CochainComplex C ℤ) ⟶
      (V.filtration.decalage.step a : CochainComplex C ℤ) :=
  (decalage_map_preserves t a).choose

@[reassoc]
theorem decalageStepMap_arrow
    {U V : FilteredObject (CochainComplex C ℤ)} (t : U ⟶ V) (a : ℤ) :
    decalageStepMap t a ≫ (V.filtration.decalage.step a).arrow =
      (U.filtration.decalage.step a).arrow ≫ t.hom :=
  (decalage_map_preserves t a).choose_spec

/-- The decalage tower is functorial on all filtered complexes. -/
noncomputable def decalageTowerFunctor :
    FilteredObject (CochainComplex C ℤ) ⥤ (EInt ⥤ CochainComplex C ℤ) where
  obj U := U.filtration.decalageTower
  map t := decalageTowerMap t
  map_id U := by
    apply NatTrans.ext
    funext a
    apply (cancel_mono (U.filtration.decalageTowerStep a).arrow).1
    change (decalageTowerMap (𝟙 U)).app a ≫ _ = (𝟙 _) ≫ _
    rw [decalageTowerMap_app_arrow]
    change _ ≫ (𝟙 _) = (𝟙 _) ≫ _
    simp
  map_comp {U V W} t s := by
    apply NatTrans.ext
    funext a
    apply (cancel_mono (W.filtration.decalageTowerStep a).arrow).1
    change (decalageTowerMap (t ≫ s)).app a ≫ _ =
      ((decalageTowerMap t).app a ≫ (decalageTowerMap s).app a) ≫ _
    simp only [Category.assoc, decalageTowerMap_app_arrow,
      reassoc_of% decalageTowerMap_app_arrow]
    rfl

end CategoryTheory.DecreasingFiltration

namespace CategoryTheory.Triangulated.SpectralObject

open ComposableArrows

variable {D : Type*} [Category* D] [HasZeroObject D] [Preadditive D]
  [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
  {ι ι' : Type*} [Category* ι] [Category* ι']

/-- Change a diagram naturally before taking its spectral object. -/
noncomputable def precompMap (X : SpectralObject D ι) {F G : ι' ⥤ ι} (τ : F ⟶ G) :
    X.precomp F ⟶ X.precomp G where
  hom.app A := X.ω₁.map (Functor.whiskerLeft A τ)
  hom.naturality A B f := by
    dsimp [precomp]
    rw [← Functor.map_comp, ← Functor.map_comp]
    congr 1
    apply NatTrans.ext
    funext i
    exact τ.naturality (f.app i)
  comm f g := by
    have h := X.δ'.naturality (Functor.whiskerLeft (mk₂ f g) τ)
    have hf : (F.mapComposableArrowsObjMk₁Iso f).inv ≫
        Functor.whiskerLeft (mk₁ f) τ =
      (functorArrows ι 0 1 2).map (Functor.whiskerLeft (mk₂ f g) τ) ≫
        (G.mapComposableArrowsObjMk₁Iso f).inv := by
      apply NatTrans.ext
      funext i
      fin_cases i
      · change (𝟙 _) ≫ τ.app _ = τ.app _ ≫ (𝟙 _)
        simp only [Category.id_comp, Category.comp_id]
      · change (𝟙 _) ≫ τ.app _ = τ.app _ ≫ (𝟙 _)
        simp only [Category.id_comp, Category.comp_id]
    have hg : Functor.whiskerLeft (mk₁ g) τ ≫
        (G.mapComposableArrowsObjMk₁Iso g).hom =
      (F.mapComposableArrowsObjMk₁Iso g).hom ≫
        (functorArrows ι 1 2 2).map (Functor.whiskerLeft (mk₂ f g) τ) := by
      apply NatTrans.ext
      funext i
      fin_cases i
      · change τ.app _ ≫ (𝟙 _) = (𝟙 _) ≫ τ.app _
        simp only [Category.id_comp, Category.comp_id]
      · change τ.app _ ≫ (𝟙 _) = (𝟙 _) ≫ τ.app _
        simp only [Category.id_comp, Category.comp_id]
    dsimp [precomp, δ]
    rw [Category.assoc, Category.assoc, ← Functor.map_comp, ← Functor.map_comp]
    change X.ω₁.map (F.mapComposableArrowsObjMk₁Iso g).hom ≫
      X.δ'.app ((F.mapComposableArrows 2).obj (mk₂ f g)) ≫
        (shiftFunctor D (1 : ℤ)).map
        (X.ω₁.map ((F.mapComposableArrowsObjMk₁Iso f).inv ≫
          Functor.whiskerLeft (mk₁ f) τ)) = _
    change X.ω₁.map ((functorArrows ι 1 2 2).map
        (Functor.whiskerLeft (mk₂ f g) τ)) ≫ X.δ'.app _ =
      X.δ'.app _ ≫ (shiftFunctor D (1 : ℤ)).map (X.ω₁.map
        ((functorArrows ι 0 1 2).map (Functor.whiskerLeft (mk₂ f g) τ))) at h
    rw [hf, Functor.map_comp, Functor.map_comp]
    erw [← reassoc_of% h, ← Functor.map_comp_assoc, ← hg, Functor.map_comp_assoc]
    rfl


end CategoryTheory.Triangulated.SpectralObject

namespace CategoryTheory.Triangulated.SpectralObject

variable {D : Type*} [Category* D] [HasZeroObject D] [Preadditive D]
  [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
  {ι ι' : Type*} [Category* ι] [Category* ι']

/-- Form spectral objects functorially from diagrams in the indexing category. -/
noncomputable def precompFunctor (X : SpectralObject D ι) :
    (ι' ⥤ ι) ⥤ SpectralObject D ι' where
  obj F := X.precomp F
  map τ := X.precompMap τ
  map_id F := by
    apply hom_ext
    apply NatTrans.ext
    funext A
    dsimp [precompMap]
    change X.ω₁.map (𝟙 (A ⋙ F)) = 𝟙 _
    exact X.ω₁.map_id _
  map_comp τ σ := by
    apply hom_ext
    apply NatTrans.ext
    funext A
    dsimp [precompMap]
    change X.ω₁.map (Functor.whiskerLeft A τ ≫ Functor.whiskerLeft A σ) =
      X.ω₁.map (Functor.whiskerLeft A τ) ≫ X.ω₁.map (Functor.whiskerLeft A σ)
    exact X.ω₁.map_comp _ _

end CategoryTheory.Triangulated.SpectralObject

namespace CategoryTheory

variable (C : Type u) [Category.{v} C] [Abelian C]

/-- Take mapping cones in the decalage tower and then their cohomology.
This construction uses actual subcomplexes and actual mapping cones throughout.
Source: Stacks Project, Tags 015X and 012K
(blueprint: def-sp-filtered-complex-decalage-tower). -/
noncomputable def filteredComplexDecalageSpectralObjectFunctor :
    FilteredObject (CochainComplex C ℤ) ⥤ Abelian.SpectralObject C EInt :=
  DecreasingFiltration.decalageTowerFunctor ⋙
    (HomotopyCategory.spectralObjectMappingCone C).precompFunctor ⋙
    (HomotopyCategory.homologyFunctor C (.up ℤ) 0).mapHomologicalSpectralObject EInt

end CategoryTheory

namespace CategoryTheory.DecreasingFiltration

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {K : CochainComplex C ℤ}

/-- A chain map lying in the shifted steps factors uniquely through decalage.
This is the restriction used for augmented upper truncations.
Source: Stacks Project, Tag 015X (blueprint: def-sp-filtered-complex-decalage-tower).

Proof. The stated condition gives the first factor of the decalage intersection.
The chain-map equation and the same condition in the next degree give its second
factor. Restrict in each degree and cancel the monic inclusions to prove the
chain-map equation and uniqueness. -/
theorem decalage_factor_iff {K' : CochainComplex C ℤ} (F : DecreasingFiltration K)
    (a : ℤ) (f : K' ⟶ K) :
    (∃! g : K' ⟶ (F.decalage.step a : CochainComplex C ℤ),
      g ≫ (F.decalage.step a).arrow = f) ↔
      ∀ n : ℤ, imageSubobject (f.f n) ≤ F.complexStep (a + n) n := by
  constructor
  · rintro ⟨g, hg, _⟩ n
    have hh := congrArg (fun k ↦ k.f n) hg
    rw [HomologicalComplex.comp_f] at hh
    calc
      imageSubobject (f.f n) ≤ F.decalage.complexStep a n := by
        rw [← hh]
        exact imageSubobject_comp_le _ _
      _ ≤ F.complexStep (a + n) n := by
        rw [F.decalage_complexStep]
        exact inf_le_left
  · intro h
    have hf (n : ℤ) : (F.complexStep (a + n) n).Factors (f.f n) := by
      apply Subobject.factors_of_le _ (h n)
      simpa only [Category.id_comp] using
        imageSubobject_factors_comp_self (f.f n) (𝟙 _)
    have hd (n : ℤ) : (F.decalage.complexStep a n).Factors (f.f n) := by
      rw [F.decalage_complexStep]
      apply (Subobject.inf_factors _).mpr
      refine ⟨hf n, (pullback_factors_iff _ _ _).mpr ?_⟩
      rw [f.comm n (n + 1)]
      have hh : (F.complexStep (a + n + 1) (n + 1)).Factors (f.f (n + 1)) := by
        simpa only [add_assoc] using hf (n + 1)
      rw [← Subobject.factorThru_arrow _ _ hh, ← Category.assoc]
      apply Subobject.factors_comp_arrow
    have hx (n : ℤ) : ∃ k : K'.X n ⟶ (F.decalage.step a : CochainComplex C ℤ).X n,
        k ≫ (F.decalage.step a).arrow.f n = f.f n := by
      have hn := hd n
      rw [complexStep, imageSubobject_mono, Subobject.mk_factors_iff] at hn
      exact hn
    choose k hk using hx
    let g : K' ⟶ (F.decalage.step a : CochainComplex C ℤ) :=
      { f := k
        comm' := by
          intro i j hij
          apply (cancel_mono ((F.decalage.step a).arrow.f j)).1
          rw [Category.assoc, ← (F.decalage.step a).arrow.comm,
            ← Category.assoc, hk, Category.assoc, hk, f.comm] }
    refine ⟨g, ?_, ?_⟩
    · ext n
      exact hk n
    · intro g' hg'
      apply (cancel_mono (F.decalage.step a).arrow).1
      exact hg'.trans (by ext n; exact (hk n).symm)

/-- The actual short exact complex for an interval of the decalage tower. -/
noncomputable def decalageTowerInterval (F : DecreasingFiltration K)
    (a b : EInt) (h : a ≤ b) : ShortComplex (CochainComplex C ℤ) :=
  ShortComplex.mk (F.decalageTower.map (homOfLE h))
    (cokernel.π (F.decalageTower.map (homOfLE h))) (cokernel.condition _)

/-- Every interval inclusion is monic, so its cokernel sequence is short exact. -/
theorem decalageTowerInterval_shortExact (F : DecreasingFiltration K)
    (a b : EInt) (h : a ≤ b) : (F.decalageTowerInterval a b h).ShortExact := by
  have : Mono (F.decalageTower.map (homOfLE h)) := by
    dsimp [decalageTower]
    infer_instance
  change (ShortComplex.mk (F.decalageTower.map (homOfLE h))
    (cokernel.π _) (cokernel.condition _)).ShortExact
  exact ⟨ShortComplex.exact_cokernel _⟩

/-- The cone-to-quotient comparison uses the specified cokernel projection. -/
noncomputable def decalageTowerConeToQuotient (F : DecreasingFiltration K)
    (a b : EInt) (h : a ≤ b) :
    CochainComplex.mappingCone (F.decalageTower.map (homOfLE h)) ⟶
      (F.decalageTowerInterval a b h).X₃ :=
  CochainComplex.mappingCone.descShortComplex (F.decalageTowerInterval a b h)

/-- The interval mapping cone computes its quotient, including at infinite endpoints. -/
theorem decalageTowerConeToQuotient_quasiIso (F : DecreasingFiltration K)
    (a b : EInt) (h : a ≤ b) : QuasiIso (F.decalageTowerConeToQuotient a b h) :=
  CochainComplex.mappingCone.quasiIso_descShortComplex
    (F.decalageTowerInterval_shortExact a b h)

/-- The cone-to-quotient comparison is normalized on the larger step. -/
theorem decalageTower_inr_coneToQuotient (F : DecreasingFiltration K)
    (a b : EInt) (h : a ≤ b) :
    CochainComplex.mappingCone.inr (F.decalageTower.map (homOfLE h)) ≫
        F.decalageTowerConeToQuotient a b h =
      cokernel.π (F.decalageTower.map (homOfLE h)) :=
  CochainComplex.mappingCone.inr_descShortComplex (F.decalageTowerInterval a b h)

/-- The resulting interval cohomology comparison. -/
noncomputable def decalageTowerConeHomologyIso (F : DecreasingFiltration K)
    (a b : EInt) (h : a ≤ b) (n : ℤ) :
    (CochainComplex.mappingCone (F.decalageTower.map (homOfLE h))).homology n ≅
      (F.decalageTowerInterval a b h).X₃.homology n := by
  have := F.decalageTowerConeToQuotient_quasiIso a b h
  exact isoOfQuasiIsoAt (F.decalageTowerConeToQuotient a b h) n

/-- A filtered map induces the actual quotient map on every tower interval. -/
noncomputable def decalageTowerIntervalMap
    {U V : FilteredObject (CochainComplex C ℤ)} (t : U ⟶ V)
    (a b : EInt) (h : a ≤ b) :
    U.filtration.decalageTowerInterval a b h ⟶
      V.filtration.decalageTowerInterval a b h where
  τ₁ := (decalageTowerMap t).app a
  τ₂ := (decalageTowerMap t).app b
  τ₃ := cokernel.map _ _ ((decalageTowerMap t).app a)
    ((decalageTowerMap t).app b) ((decalageTowerMap t).naturality (homOfLE h))
  comm₁₂ := ((decalageTowerMap t).naturality (homOfLE h)).symm
  comm₂₃ := (cokernel.π_desc _ _ _).symm

/-- The interval comparison commutes with every filtered map. -/
theorem decalageTowerConeToQuotient_naturality
    {U V : FilteredObject (CochainComplex C ℤ)} (t : U ⟶ V)
    (a b : EInt) (h : a ≤ b) :
    CochainComplex.mappingCone.map
        (U.filtration.decalageTower.map (homOfLE h))
        (V.filtration.decalageTower.map (homOfLE h))
        ((decalageTowerMap t).app a) ((decalageTowerMap t).app b)
        ((decalageTowerMap t).naturality (homOfLE h)) ≫
        V.filtration.decalageTowerConeToQuotient a b h =
      U.filtration.decalageTowerConeToQuotient a b h ≫
        (decalageTowerIntervalMap t a b h).τ₃ :=
  CochainComplex.mappingCone.descShortComplex_naturality
    (decalageTowerIntervalMap t a b h)

/-- For finite endpoints the cokernel is the ordinary quotient of decalage steps. -/
theorem decalageTowerInterval_coe (F : DecreasingFiltration K)
    (a b : ℤ) (h : a ≤ b) :
    (F.decalageTowerInterval a b (by simpa using h)).X₃ =
      F.decalage.complexQuotient (1 - b) (1 - a) (by omega) := rfl

end CategoryTheory.DecreasingFiltration

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Interval cohomology of the constructed spectral object is quotient cohomology.
The comparison is induced by the canonical cone-to-cokernel map. -/
noncomputable def filteredComplexDecalageIntervalIso
    (U : FilteredObject (CochainComplex C ℤ)) (a b : EInt) (h : a ≤ b) (n : ℤ) :
    (((filteredComplexDecalageSpectralObjectFunctor C).obj U).H n).obj
        (ComposableArrows.mk₁ (homOfLE h)) ≅
      (U.filtration.decalageTowerInterval a b h).X₃.homology n :=
  (HomotopyCategory.homologyFunctorFactors C (.up ℤ) n).app
    (CochainComplex.mappingCone (U.filtration.decalageTower.map (homOfLE h))) ≪≫
    U.filtration.decalageTowerConeHomologyIso a b h n

/-- The interval cohomology comparison commutes with the specified quotient maps. -/
@[reassoc]
theorem filteredComplexDecalageIntervalIso_naturality
    {U V : FilteredObject (CochainComplex C ℤ)} (t : U ⟶ V)
    (a b : EInt) (h : a ≤ b) (n : ℤ) :
    (((filteredComplexDecalageSpectralObjectFunctor C).map t).hom n).app
        (ComposableArrows.mk₁ (homOfLE h)) ≫
        (filteredComplexDecalageIntervalIso V a b h n).hom =
      (filteredComplexDecalageIntervalIso U a b h n).hom ≫
        (HomologicalComplex.homologyFunctor C (.up ℤ) n).map
          (DecreasingFiltration.decalageTowerIntervalMap t a b h).τ₃ := by
  let f := CochainComplex.mappingCone.map
    (U.filtration.decalageTower.map (homOfLE h))
    (V.filtration.decalageTower.map (homOfLE h))
    ((DecreasingFiltration.decalageTowerMap t).app a)
    ((DecreasingFiltration.decalageTowerMap t).app b)
    ((DecreasingFiltration.decalageTowerMap t).naturality (homOfLE h))
  let H := HomologicalComplex.homologyFunctor C (.up ℤ) n
  let e := HomotopyCategory.homologyFunctorFactors C (.up ℤ) n
  change (HomotopyCategory.homologyFunctor C (.up ℤ) n).map
      ((HomotopyCategory.quotient C (.up ℤ)).map f) ≫
        (e.app _).hom ≫ H.map (V.filtration.decalageTowerConeToQuotient a b h) =
      ((e.app _).hom ≫ H.map (U.filtration.decalageTowerConeToQuotient a b h)) ≫
        H.map (DecreasingFiltration.decalageTowerIntervalMap t a b h).τ₃
  rw [← Category.assoc]
  erw [e.hom.naturality f]
  rw [Category.assoc, ← H.map_comp,
    DecreasingFiltration.decalageTowerConeToQuotient_naturality, H.map_comp,
    Category.assoc]
  rfl

end CategoryTheory
