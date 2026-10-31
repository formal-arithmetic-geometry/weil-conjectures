/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.AdicQbarRealization.Reindex.AdicReindexScalarChartVertices
import WeilConjectures.SixFunctors.AdicQbarRealization.Reindex.AdicReindexScalarChartScalarEquation
import all WeilConjectures.AlgebraicGeometry.Pbc.PbcRationalAutomorphismScalarCoherence
import WeilConjectures.SixFunctors.IntegralFiniteExtension.IntegralScalarComplexCounitComparison
import all Mathlib.CategoryTheory.Limits.HasLimits

/-! # Representative equations for scalar reindexing computation charts

Source: Stacks 06YY and 07A4; Bhatt--Scholze, Proposition 6.8.14.
(blueprint: lem-sf-adic-reindex-scalar-chart-equations).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
attribute [local irreducible] HasDerivedCategory.standard
  WeilConjectures.podCompletedRingMap
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.AdicQbarRealization
open AlgebraicallyClosedCoefficients (Index Coefficient coefficientInclusion)

structure ScalarComputationChartEquations {D : Type*} [Category D] {ι : Type*}
    {Good : ι → Prop} {V₀ V₁ V₂ V₃ V₄ : D}
    {f₀ : V₀ ⟶ V₁} {f₁ : V₁ ⟶ V₂} {f₂ : V₂ ⟶ V₃}
    {d : V₃ ⟶ V₄} {u : V₀ ⟶ V₄}
    {W₀ W₁ W₂ W₃ W₄ : ι → D}
    {c₀ : ∀ P, W₀ P ⟶ W₁ P} {c₁ : ∀ P, W₁ P ⟶ W₂ P}
    {c₂ : ∀ P, W₂ P ⟶ W₃ P} {c₃ : ∀ P, W₃ P ⟶ W₄ P}
    {c : ∀ P, W₀ P ⟶ W₄ P}
    (t : ScalarComputationChartVertices Good V₀ V₁ V₂ V₃ V₄ f₀ f₁ f₂ d u
      W₀ W₁ W₂ W₃ W₄ c₀ c₁ c₂ c₃ c) where
  h₀ : f₀ ≫ t.v₁.hom = t.v₀.hom ≫ c₀ t.P
  h₁ : f₁ ≫ t.v₂.hom = t.v₁.hom ≫ c₁ t.P
  h₂ : f₂ ≫ t.v₃.hom = t.v₂.hom ≫ c₂ t.P
  h₃ : d ≫ t.v₄.hom = t.v₃.hom ≫ c₃ t.P
  h₄ : u ≫ t.v₄.hom = t.v₀.hom ≫ c t.P

private theorem balance_transport {A B C D : Type*}
    [Category A] [Category B] [Category C] [Category D]
    (E : A ⥤ B) (F : B ⥤ D) (H : A ⥤ C) (R : C ⥤ D)
    (β : E ⋙ F ≅ H ⋙ R) {U V : A} (a : U ⟶ V)
    {X : C} {Y : B} {Z W : D}
    (ch : H.obj V ⟶ X) (cx : R.obj X ⟶ Z)
    (cy : E.obj V ⟶ Y) (cf : F.obj Y ⟶ W) (b : W ≅ Z)
    (h : β.hom.app V ≫ R.map ch ≫ cx = F.map cy ≫ cf ≫ b.hom) :
    β.inv.app U ≫ F.map (E.map a) ≫ F.map cy ≫ cf =
      R.map (H.map a) ≫ R.map ch ≫ cx ≫ b.inv := by
  have hr : β.inv.app V ≫ (F.map cy ≫ cf) = (R.map ch ≫ cx) ≫ b.inv := by
    have hh := congrArg (fun z ↦ β.inv.app V ≫ z ≫ b.inv) h
    simpa only [Category.assoc, Iso.inv_hom_id_app_assoc,
      Iso.hom_inv_id, Category.comp_id] using hh.symm
  have hn := β.inv.naturality a
  dsimp only [Functor.comp_map] at hn
  calc
    _ = (β.inv.app U ≫ F.map (E.map a)) ≫ (F.map cy ≫ cf) := by simp [Category.assoc]
    _ = (R.map (H.map a) ≫ β.inv.app V) ≫ (F.map cy ≫ cf) := by rw [← hn]
    _ = R.map (H.map a) ≫ ((R.map ch ≫ cx) ≫ b.inv) := by
      rw [Category.assoc, hr]
    _ = _ := by simp [Category.assoc]

private theorem balance_transport_two {A B C D : Type*}
    [Category A] [Category B] [Category C] [Category D]
    (E : A ⥤ B) (F : B ⥤ D) (H : A ⥤ C) (R : C ⥤ D)
    (β : E ⋙ F ≅ H ⋙ R) {U V T : A} (a : U ⟶ V) (a' : V ⟶ T)
    {X : C} {Y : B} {Z W : D}
    (ch : H.obj T ⟶ X) (cx : R.obj X ⟶ Z)
    (cy : E.obj T ⟶ Y) (cf : F.obj Y ⟶ W) (b : W ≅ Z)
    (h : β.hom.app T ≫ R.map ch ≫ cx = F.map cy ≫ cf ≫ b.hom) :
    β.inv.app U ≫ F.map (E.map a) ≫ F.map (E.map a') ≫ F.map cy ≫ cf =
      (R.map (H.map a) ≫ R.map (H.map a') ≫ R.map ch ≫ cx) ≫ b.inv := by
  simpa only [Functor.map_comp, Category.assoc] using
    balance_transport E F H R β (a ≫ a') ch cx cy cf b h

private theorem assoc_four {D : Type*} [Category D] {A B C E F : D}
    (f : A ⟶ B) (g : B ⟶ C) (h : C ⟶ E) (i : E ⟶ F) :
    f ≫ g ≫ h ≫ i = (f ≫ g ≫ h) ≫ i := by simp only [Category.assoc]

private theorem map_three_four {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {X A B Y A' B' C' : C} {U V : D}
    (f₀ : X ⟶ A) (f₁ : A ⟶ B) (f₂ : B ⟶ Y)
    (g₀ : X ⟶ A') (g₁ : A' ⟶ B') (g₂ : B' ⟶ C') (g₃ : C' ⟶ Y)
    (ε : F.obj Y ⟶ V) (ε' : F.obj C' ⟶ U) (c : U ⟶ V)
    (h : f₀ ≫ f₁ ≫ f₂ = g₀ ≫ g₁ ≫ g₂ ≫ g₃)
    (hc : F.map g₃ ≫ ε = ε' ≫ c) :
    F.map f₀ ≫ F.map f₁ ≫ F.map f₂ ≫ ε =
      F.map g₀ ≫ F.map g₁ ≫ F.map g₂ ≫ ε' ≫ c := by
  have hh := congrArg (fun z ↦ F.map z ≫ ε) h
  simpa only [Functor.map_comp, Category.assoc, hc] using hh

private theorem normalization (W : Scheme.{u})
    {A C D : Sheaf (ProEt.topology W) CommRingCat.{u + 1}}
    (a : A ⟶ C) (b : C ⟶ D) (c : A ⟶ D) (w : a ≫ b = c)
    (P : CochainComplex (pbcModules W A) ℤ) :
    (pbcReductionNormalization a b c w (DerivedCategory.Q.obj P)).hom ≫
        pbcComplexCounit c P =
      (pbcDerivedExtend b).map (pbcComplexCounit a P) ≫
        pbcComplexCounit b (((pbcExtend a).mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map ((Functor.mapHomologicalComplexCompIso
          (Adjunction.leftAdjointCompIso (pbcScalarAdjunction a) (pbcScalarAdjunction b)
            (pbcScalarAdjunction c) (pbcRestrictComp a b c w)) (.up ℤ)).hom.app P) := by
  have he : (pbcReductionNormalization a b c w (DerivedCategory.Q.obj P)).hom =
      (Adjunction.leftAdjointCompIso (pbcDerivedScalarAdjunction a)
        (pbcDerivedScalarAdjunction b) (pbcDerivedScalarAdjunction c)
        (pbcDerivedRestrictComp a b c w)).hom.app (DerivedCategory.Q.obj P) := by
    dsimp [pbcReductionNormalization, pbcReductionNormalizationHom, pbcReductionTransition]
    simp only [Adjunction.leftAdjointCompIso_hom_app, Adjunction.homEquiv_counit,
      Functor.map_comp, Category.assoc, asIso_hom]
  rw [he]
  exact extensionAssociator_normalization a b c w P

private theorem inverse_transport {C D : Type*} [Category C] [Category D]
    {F G : C ⥤ D} (β : F ≅ G) {U V : C} (a : U ⟶ V)
    {W Z : D} (f : F.obj V ⟶ W) (g : G.obj V ⟶ Z) (b : W ≅ Z)
    (h : β.hom.app V ≫ g = f ≫ b.hom) :
    β.inv.app U ≫ F.map a ≫ f = G.map a ≫ g ≫ b.inv := by
  have hn := β.inv.naturality a
  have hr : β.inv.app V ≫ f = g ≫ b.inv := by
    have hh := congrArg (fun z ↦ β.inv.app V ≫ z ≫ b.inv) h
    simpa only [Category.assoc, Iso.inv_hom_id_app_assoc,
      Iso.hom_inv_id, Category.comp_id] using hh.symm
  calc
    _ = (β.inv.app U ≫ F.map a) ≫ f := by simp only [Category.assoc]
    _ = (G.map a ≫ β.inv.app V) ≫ f := by rw [← hn]
    _ = G.map a ≫ g ≫ b.inv := by rw [Category.assoc, hr]

private theorem inverse_transport_two {C D : Type*} [Category C] [Category D]
    {F G : C ⥤ D} (β : F ≅ G) {U V T : C} (a : U ⟶ V) (b : V ⟶ T)
    {W Z : D} (f : F.obj T ⟶ W) (g : G.obj T ⟶ Z) (c : W ≅ Z)
    (h : β.hom.app T ≫ g = f ≫ c.hom) :
    β.inv.app U ≫ F.map a ≫ F.map b ≫ f =
      (G.map a ≫ G.map b ≫ g) ≫ c.inv := by
  simpa only [Functor.map_comp, Category.assoc] using
    inverse_transport β (a ≫ b) f g c h

private theorem assoc_five {D : Type*} [Category D] {A B C E F G : D}
    (f : A ⟶ B) (g : B ⟶ C) (h : C ⟶ E) (i : E ⟶ F) (j : F ⟶ G) :
    f ≫ g ≫ h ≫ i ≫ j = (f ≫ g ≫ h ≫ i) ≫ j := by simp only [Category.assoc]

set_option maxHeartbeats 1200000 in
-- Convert the two universal scalar models and their cochain adjunctions.
private theorem native_normalization (l : ℕ) [Fact l.Prime] (W : Scheme.{u})
    (R : LocallyFiniteAdicRealization.Realization l W)
    (E L : Index l (PadicAlgCl l)) (h : E ≤ L)
    (P : CochainComplex (integralTowerModules l (Coefficient.{u} l (PadicAlgCl l) E) W) ℤ) :
    (pbcReductionNormalization
      (completedCoefficientMap l (Coefficient.{u} l (PadicAlgCl l) E)
        (Coefficient.{u} l (PadicAlgCl l) L) (coefficientInclusion l (PadicAlgCl l) E L h) W)
      (coefficientMap l W R L) (coefficientMap l W R E)
      (R.coefficient_scalar E L h) (DerivedCategory.Q.obj P)).hom ≫
        pbcComplexCounit (coefficientMap l W R E) P =
    (pbcDerivedExtend (coefficientMap l W R L)).map
      (completedScalarCounit l (Coefficient.{u} l (PadicAlgCl l) E)
        (Coefficient.{u} l (PadicAlgCl l) L) (coefficientInclusion l (PadicAlgCl l) E L h) W P) ≫
      pbcComplexCounit (coefficientMap l W R L)
        ((completedOrdinaryScalarComplex l (Coefficient.{u} l (PadicAlgCl l) E)
          (Coefficient.{u} l (PadicAlgCl l) L)
          (coefficientInclusion l (PadicAlgCl l) E L h) W).obj P) ≫
      DerivedCategory.Q.map ((Functor.mapHomologicalComplexCompIso
        (nativeScalarSheafAssociator l W R E L h) (.up ℤ)).hom.app P) := by
  have hh := normalization W
    (completedCoefficientMap l (Coefficient.{u} l (PadicAlgCl l) E)
      (Coefficient.{u} l (PadicAlgCl l) L)
      (coefficientInclusion l (PadicAlgCl l) E L h) W)
    (coefficientMap l W R L) (coefficientMap l W R E) (R.coefficient_scalar E L h) P
  rw [WeilConjectures.IntegralFiniteExtension.pbcComplexCounit_eq_completedScalarCounit]
    at hh
  with_unfolding_all exact hh

set_option maxHeartbeats 2400000 in
-- Elaborate the specified nested derived and cochain comparison functors.
/-- The two associator edges for the specified counit maps.
Source: Stacks 07A4; BS 6.8.14--6.8.15.
(blueprint: lem-sf-adic-reindex-scalar-chart-equations).

Proof in words: the ordinary adjunctions on complexes have the prescribed tensor
units. Cochain adjunction compatibility identifies their derived units. Uniqueness
of normalized adjunction composition then identifies the derived comparison with
pbcReductionNormalization and the ordinary comparison with
nativeScalarSheafAssociator. Apply this at the X-side pulled-back representative
and at P on Y, then apply the exact reindexing factorization on Y. Naturality
transports both equations along e.inv. No scalar-reindexing or balance equation
is used in either associator calculation.
-/
theorem adic_scalar_chart_associator_equations (l : ℕ) [Fact l.Prime]
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (R : LocallyFiniteAdicRealization.Realization l X)
    (S : LocallyFiniteAdicRealization.Realization l Y)
    (B : RingReindex l X g R S)
    (E L : Index l (PadicAlgCl l)) (h : E ≤ L)
    (be : pbcExtend (coefficientMap l Y S E) ⋙ modulePull l X g B ≅
      podCompletedModuleInverseImage l (Coefficient.{u} l (PadicAlgCl l) E) g ⋙
        pbcExtend (coefficientMap l X R E))
    (bl : pbcExtend (coefficientMap l Y S L) ⋙ modulePull l X g B ≅
      podCompletedModuleInverseImage l (Coefficient.{u} l (PadicAlgCl l) L) g ⋙
        pbcExtend (coefficientMap l X R L))
    (de : pbcDerivedExtend (coefficientMap l Y S E) ⋙ derivedPull l X g B ≅
      podCompletedDerivedInverseImage l (Coefficient.{u} l (PadicAlgCl l) E) g ⋙
        pbcDerivedExtend (coefficientMap l X R E))
    (dl : pbcDerivedExtend (coefficientMap l Y S L) ⋙ derivedPull l X g B ≅
      podCompletedDerivedInverseImage l (Coefficient.{u} l (PadicAlgCl l) L) g ⋙
        pbcDerivedExtend (coefficientMap l X R L))
    (K : DerivedCategory (integralTowerModules l (Coefficient.{u} l (PadicAlgCl l) E) Y))
    (P : CochainComplex (integralTowerModules l (Coefficient.{u} l (PadicAlgCl l) E) Y) ℤ)
    (e : DerivedCategory.Q.obj P ≅ K)
    (hp : CochainComplex.IsKFlatIndependentCoefficients
      (R := completedIntegralCommRingSheafUnrestricted l
        (Coefficient.{u} l (PadicAlgCl l) E) Y) P)
    (hf : ∀ n : ℤ, SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
      (R := completedIntegralCommRingSheafUnrestricted l
        (Coefficient.{u} l (PadicAlgCl l) E) Y) (P.X n)) :
    (adicScalarChartVertices l g R S B E L h be bl de dl K P e hp hf).associatorEquations := by
  let A := Coefficient.{u} l (PadicAlgCl l) E
  let C := Coefficient.{u} l (PadicAlgCl l) L
  let i := coefficientInclusion l (PadicAlgCl l) E L h
  let HE := podCompletedModuleInverseImage l A g
  let rE := pbcDerivedExtend (coefficientMap l X R E)
  let rL := pbcDerivedExtend (coefficientMap l X R L)
  let sE := pbcDerivedExtend (coefficientMap l Y S E)
  let sL := pbcDerivedExtend (coefficientMap l Y S L)
  let TX := completedDerivedScalarExtension l A C i X
  let TY := completedDerivedScalarExtension l A C i Y
  let βX := Adjunction.leftAdjointCompIso
    (pbcDerivedScalarAdjunction (completedCoefficientMap l A C i X))
    (pbcDerivedScalarAdjunction (coefficientMap l X R L))
    (pbcDerivedScalarAdjunction (coefficientMap l X R E))
    (pbcDerivedRestrictComp _ _ _ (R.coefficient_scalar E L h))
  let βY := Adjunction.leftAdjointCompIso
    (pbcDerivedScalarAdjunction (completedCoefficientMap l A C i Y))
    (pbcDerivedScalarAdjunction (coefficientMap l Y S L))
    (pbcDerivedScalarAdjunction (coefficientMap l Y S E))
    (pbcDerivedRestrictComp _ _ _ (S.coefficient_scalar E L h))
  have hβX (M) : pbcReductionNormalization (completedCoefficientMap l A C i X)
      (coefficientMap l X R L) (coefficientMap l X R E)
      (R.coefficient_scalar E L h) M = βX.app M := by
    apply Iso.ext
    dsimp [pbcReductionNormalization, pbcReductionNormalizationHom, pbcReductionTransition, βX]
    simp only [Adjunction.leftAdjointCompIso_hom_app, Adjunction.homEquiv_counit,
      Functor.map_comp, Category.assoc, asIso_hom]
  have hβY (M) : pbcReductionNormalization (completedCoefficientMap l A C i Y)
      (coefficientMap l Y S L) (coefficientMap l Y S E)
      (S.coefficient_scalar E L h) M = βY.app M := by
    apply Iso.ext
    dsimp [pbcReductionNormalization, pbcReductionNormalizationHom, pbcReductionTransition, βY]
    simp only [Adjunction.leftAdjointCompIso_hom_app, Adjunction.homEquiv_counit,
      Functor.map_comp, Category.assoc, asIso_hom]
  dsimp only [ScalarComputationChartVertices.associatorEquations]
  constructor
  · let Q := (HE.mapHomologicalComplex (.up ℤ)).obj P
    have hn := native_normalization l X R E L h Q
    rw [hβX] at hn
    have hh := inverse_transport_two βX
      ((podCompletedDerivedInverseImage l A g).map e.inv)
      (HE.mapDerivedCategoryFactors.hom.app P)
      (rL.map (completedScalarCounit l A C i X Q) ≫
        pbcComplexCounit (coefficientMap l X R L)
          ((completedOrdinaryScalarComplex l A C i X).obj Q))
      (pbcComplexCounit (coefficientMap l X R E) Q)
      (DerivedCategory.Q.mapIso ((Functor.mapHomologicalComplexCompIso
        (nativeScalarSheafAssociator l X R E L h) (.up ℤ)).app Q)) (by
          dsimp only [rL, Q, HE, A, C, i, Functor.comp_obj] at hn ⊢
          dsimp only [Functor.mapIso, Iso.app] at ⊢
          dsimp only [Iso.app] at hn
          with_unfolding_all exact hn.trans (Category.assoc _ _ _).symm)
    dsimp only [Functor.mapIso, Iso.app] at hh
    dsimp only [adicScalarChartVertices, adicScalarChartMap₀, adicScalarChartMap₁,
      asIso] at ⊢
    dsimp only [rL, rE, TX, HE, Q, A, C, i] at hh
    erw [hβX]
    dsimp only [Functor.comp_map, Iso.app] at hh ⊢
    with_unfolding_all exact hh
  · let Q := (completedOrdinaryScalarComplex l A C i Y).obj P
    let b := (Functor.mapHomologicalComplexCompIso
      (nativeScalarSheafAssociator l Y S E L h) (.up ℤ)).hom.app P
    have hn := native_normalization l Y S E L h P
    rw [hβY] at hn
    have hy : βY.hom.app K ≫ sE.map e.inv ≫
        pbcComplexCounit (coefficientMap l Y S E) P =
      sL.map (TY.map e.inv) ≫ sL.map (completedScalarCounit l A C i Y P) ≫
        pbcComplexCounit (coefficientMap l Y S L) Q ≫ DerivedCategory.Q.map b := by
      have hh := congrArg (fun z ↦ z ≫
        pbcComplexCounit (coefficientMap l Y S E) P) (βY.hom.naturality e.inv).symm
      have hi := congrArg (fun z ↦ sL.map (TY.map e.inv) ≫ z) hn
      dsimp only [Functor.comp_map, Functor.comp_obj, sE, sL, TY, Q, b,
        completedDerivedScalarExtension] at hh hi ⊢
      with_unfolding_all simp only [Category.assoc] at hh
      with_unfolding_all simpa only [Category.assoc] using hh.trans hi
    have ht :=  (modulePull l X g B).mapDerivedCategoryFactors.hom.naturality b
    dsimp only [Functor.comp_map] at ht
    have hh := map_three_four (derivedPull l X g B) (βY.hom.app K)
      (sE.map e.inv) (pbcComplexCounit (coefficientMap l Y S E) P)
      (sL.map (TY.map e.inv)) (sL.map (completedScalarCounit l A C i Y P))
      (pbcComplexCounit (coefficientMap l Y S L) Q) (DerivedCategory.Q.map b)
      ((modulePull l X g B).mapDerivedCategoryFactors.hom.app
        (((pbcExtend (coefficientMap l Y S E)).mapHomologicalComplex (.up ℤ)).obj P))
      ((modulePull l X g B).mapDerivedCategoryFactors.hom.app
        (((pbcExtend (coefficientMap l Y S L)).mapHomologicalComplex (.up ℤ)).obj Q))
      (DerivedCategory.Q.map (((modulePull l X g B).mapHomologicalComplex (.up ℤ)).map b))
      hy (by with_unfolding_all exact ht)
    dsimp only [adicScalarChartVertices, adicScalarChartMap₃, adicScalarChartMap₄,
      asIso] at ⊢
    erw [hβY]
    dsimp only [sL, sE, TY, Q, b, A, C, i] at hh
    dsimp only [Iso.app] at ⊢
    refine hh.trans ?_
    exact assoc_five
      ((derivedPull l X g B).map ((pbcDerivedExtend (coefficientMap l Y S L)).map
        ((completedDerivedScalarExtension l _ _
          (coefficientInclusion l (PadicAlgCl l) E L h) Y).map e.inv)))
      _ _ _ _

set_option maxHeartbeats 800000 in
-- Elaborate the five squares over the same concrete representative.
/-- Assemble the scalar and associator edges with the balance representative equations.
Source: Stacks 06YY and 07A4 (blueprint: lem-sf-adic-reindex-scalar-chart-equations). -/
theorem adic_scalar_chart_equations (l : ℕ) [Fact l.Prime]
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (R : LocallyFiniteAdicRealization.Realization l X)
    (S : LocallyFiniteAdicRealization.Realization l Y)
    (B : RingReindex l X g R S)
    (E L : Index l (PadicAlgCl l)) (h : E ≤ L)
    (be : pbcExtend (coefficientMap l Y S E) ⋙ modulePull l X g B ≅
      podCompletedModuleInverseImage l (Coefficient.{u} l (PadicAlgCl l) E) g ⋙
        pbcExtend (coefficientMap l X R E))
    (bl : pbcExtend (coefficientMap l Y S L) ⋙ modulePull l X g B ≅
      podCompletedModuleInverseImage l (Coefficient.{u} l (PadicAlgCl l) L) g ⋙
        pbcExtend (coefficientMap l X R L))
    (de : pbcDerivedExtend (coefficientMap l Y S E) ⋙ derivedPull l X g B ≅
      podCompletedDerivedInverseImage l (Coefficient.{u} l (PadicAlgCl l) E) g ⋙
        pbcDerivedExtend (coefficientMap l X R E))
    (dl : pbcDerivedExtend (coefficientMap l Y S L) ⋙ derivedPull l X g B ≅
      podCompletedDerivedInverseImage l (Coefficient.{u} l (PadicAlgCl l) L) g ⋙
        pbcDerivedExtend (coefficientMap l X R L))
    (hE : integralReindexRepresentative l X g B E be de)
    (hL : integralReindexRepresentative l X g B L bl dl)
    (K : DerivedCategory (integralTowerModules l (Coefficient.{u} l (PadicAlgCl l) E) Y))
    (P : CochainComplex (integralTowerModules l (Coefficient.{u} l (PadicAlgCl l) E) Y) ℤ)
    (e : DerivedCategory.Q.obj P ≅ K)
    (hp : CochainComplex.IsKFlatIndependentCoefficients
      (R := completedIntegralCommRingSheafUnrestricted l
        (Coefficient.{u} l (PadicAlgCl l) E) Y) P)
    (hf : ∀ n : ℤ, SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
      (R := completedIntegralCommRingSheafUnrestricted l
        (Coefficient.{u} l (PadicAlgCl l) E) Y) (P.X n)) :
    Nonempty (ScalarComputationChartEquations
      (adicScalarChartVertices l g R S B E L h be bl de dl K P e hp hf)) := by
  have ha := adic_scalar_chart_associator_equations l g R S B E L h be bl de dl K P e hp hf
  have hs := adic_scalar_chart_scalar_equation l g R S B E L h be bl de dl K P e hp hf
  refine ⟨{ h₀ := ha.1, h₁ := hs, h₂ := ?_, h₃ := ha.2, h₄ := ?_ }⟩
  · have hh := balance_transport_two
      (pbcDerivedExtend (coefficientMap l Y S L)) (derivedPull l X g B)
      (podCompletedDerivedInverseImage l (Coefficient.{u} l (PadicAlgCl l) L) g)
      (pbcDerivedExtend (coefficientMap l X R L)) dl
      ((completedDerivedScalarExtension l (Coefficient.{u} l (PadicAlgCl l) E)
        (Coefficient.{u} l (PadicAlgCl l) L)
        (coefficientInclusion l (PadicAlgCl l) E L h) Y).map e.inv)
      (completedScalarCounit l (Coefficient.{u} l (PadicAlgCl l) E)
          (Coefficient.{u} l (PadicAlgCl l) L)
          (coefficientInclusion l (PadicAlgCl l) E L h) Y P)
      ((podCompletedModuleInverseImage l (Coefficient.{u} l (PadicAlgCl l) L)
        g).mapDerivedCategoryFactors.hom.app
          ((completedOrdinaryScalarComplex l (Coefficient.{u} l (PadicAlgCl l) E)
            (Coefficient.{u} l (PadicAlgCl l) L)
            (coefficientInclusion l (PadicAlgCl l) E L h) Y).obj P))
      (pbcComplexCounit (coefficientMap l X R L) _)
      (pbcComplexCounit (coefficientMap l Y S L) _)
      ((modulePull l X g B).mapDerivedCategoryFactors.hom.app _)
      (DerivedCategory.Q.mapIso ((NatIso.mapHomologicalComplex bl (.up ℤ)).app _))
      (hL _)
    dsimp only [Functor.mapIso, Iso.app] at hh
    dsimp only [adicScalarChartVertices, adicScalarChartMap₂, adicScalarChartMap₃,
      asIso] at ⊢
    with_unfolding_all exact hh
  · have hh := balance_transport
      (pbcDerivedExtend (coefficientMap l Y S E)) (derivedPull l X g B)
      (podCompletedDerivedInverseImage l (Coefficient.{u} l (PadicAlgCl l) E) g)
      (pbcDerivedExtend (coefficientMap l X R E)) de e.inv
      ((podCompletedModuleInverseImage l (Coefficient.{u} l (PadicAlgCl l) E)
        g).mapDerivedCategoryFactors.hom.app P)
      (pbcComplexCounit (coefficientMap l X R E) _)
      (pbcComplexCounit (coefficientMap l Y S E) P)
      ((modulePull l X g B).mapDerivedCategoryFactors.hom.app _)
      (DerivedCategory.Q.mapIso ((NatIso.mapHomologicalComplex be (.up ℤ)).app P))
      (hE P)
    dsimp only [Functor.mapIso, Iso.app] at hh
    dsimp only [adicScalarChartVertices, adicScalarChartMap₀, adicScalarChartMap₄,
      asIso] at ⊢
    refine hh.trans ?_
    exact assoc_four _ _ _ _

end WeilConjectures.AdicQbarRealization
