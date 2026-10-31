/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ReconstructedPairRefinementData
import WeilConjectures.AlgebraicGeometry.ReconstructedRefinementCommon
import WeilConjectures.AlgebraicGeometry.ReconstructedBrownMateLaws
import WeilConjectures.AlgebraicGeometry.ReconstructedRefinementSingleDegree
import WeilConjectures.AlgebraicGeometry.ReconstructedRefinementTraceTransport
import WeilConjectures.Compactification.CommonRefinement

/-! # Coherence of reconstructed representing pairs

Source: blueprint sk-prop-sp-unique-adjoint, categorical proof, and
sk-thm-purity-transport Steps 2--4
(blueprint: lem-pur-reconstructed-pair-refinement-coherence).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
attribute [-instance] WeilConjectures.IntegralHom.derivedCategory
attribute [-instance] WeilConjectures.integralExceptionalSystemDerived
attribute [-instance] WeilConjectures.integralExceptionalLevelDerived
attribute [local instance 5000] AlgebraicGeometry.strictEtaleLevelDerived
  AlgebraicGeometry.strictEtaleSystemDerived
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj
open WeilConjectures CompactSupportCondensedRealization PurIntegralSupportComparison
namespace WeilConjectures.ReconstructedPairRefinement

section LegacyTraceCompatibility

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false

section Abstract

private theorem conjugate_on_image
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    (e : A ≌ B) (v : C ⥤ D) (F G : B ⥤ D) (F' G' : A ⥤ C)
    (a : e.functor ⋙ F ≅ F' ⋙ v) (b : e.functor ⋙ G ≅ G' ⋙ v)
    (t : F' ⟶ G') (K : A) :
    a.inv.app K ≫ (conjugate e v F G F' G' a b t).app (e.functor.obj K) =
      v.map (t.app K) ≫ b.inv.app K := by
  unfold conjugate
  dsimp only
  unfold conjugateComponent
  rw [e.counitInv_app_functor, e.counit_app_functor]
  have ha := a.inv.naturality (e.unitIso.hom.app K)
  have ht := t.naturality (e.unitIso.hom.app K)
  dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at ha ht
  have hb := b.inv.naturality (e.unitIso.hom.app K)
  dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at hb
  calc
    _ = v.map (F'.map (e.unitIso.hom.app K)) ≫
        a.inv.app (e.inverse.obj (e.functor.obj K)) ≫
        a.hom.app (e.inverse.obj (e.functor.obj K)) ≫
        v.map (t.app (e.inverse.obj (e.functor.obj K))) ≫
        b.inv.app (e.inverse.obj (e.functor.obj K)) ≫
        G.map (e.functor.map (e.unitIso.inv.app K)) := by
      simpa only [Category.assoc, Equivalence.unit, Equivalence.unitInv] using
        congrArg (fun z ↦ z ≫ a.hom.app (e.inverse.obj (e.functor.obj K)) ≫
          v.map (t.app (e.inverse.obj (e.functor.obj K))) ≫
          b.inv.app (e.inverse.obj (e.functor.obj K)) ≫
          G.map (e.functor.map (e.unitIso.inv.app K))) ha.symm
    _ = v.map (t.app K) ≫ v.map (G'.map (e.unitIso.hom.app K)) ≫
        b.inv.app (e.inverse.obj (e.functor.obj K)) ≫
        G.map (e.functor.map (e.unitIso.inv.app K)) := by
      simp only [Iso.inv_hom_id_app_assoc]
      rw [← v.map_comp_assoc, ht, v.map_comp]
      simp only [Category.assoc]
    _ = _ := by
      rw [reassoc_of% hb]
      simp only [← G.map_comp, ← e.functor.map_comp, Iso.hom_inv_id_app]
      dsimp only [Functor.id_obj]
      rw [e.functor.map_id, G.map_id, Category.comp_id]

private theorem adjunction_detects_maps
    {A B : Type*} [Category A] [Category B]
    {R : A ⥤ B} {T : B ⥤ A} (a : R ⊣ T)
    {K L : A} [IsIso (a.unit.app L)] (f g : K ⟶ L)
    (h : R.map f = R.map g) : f = g := by
  apply (cancel_mono (a.unit.app L)).1
  calc
    f ≫ a.unit.app L = a.unit.app K ≫ T.map (R.map f) := a.unit.naturality f
    _ = a.unit.app K ≫ T.map (R.map g) := by rw [h]
    _ = g ≫ a.unit.app L := (a.unit.naturality g).symm

private theorem trace_square_of_reduction
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    (R : A ⥤ B) (V : C ⥤ D) (F₁ F₂ : B ⥤ D) (H₁ H₂ : A ⥤ C)
    (alpha₁ : H₁ ⋙ V ⟶ R ⋙ F₁) (alpha₂ : H₂ ⋙ V ⟶ R ⋙ F₂)
    (p : H₂ ⟶ H₁) (t : F₂ ⟶ F₁)
    (K₁ K₂ : A) (a : K₂ ⟶ K₁)
    (hp : V.map (p.app K₂) ≫ alpha₁.app K₂ =
      alpha₂.app K₂ ≫ t.app (R.obj K₂))
    (M₁ M₂ : B) (L : C) (s : M₂ ⟶ M₁)
    (e₁ : R.obj K₁ ⟶ M₁) (e₂ : R.obj K₂ ⟶ M₂)
    (he : R.map a ≫ e₁ = e₂ ≫ s)
    (epsilon₁ : F₁.obj M₁ ⟶ V.obj L) (epsilon₂ : F₂.obj M₂ ⟶ V.obj L)
    (hs : t.app M₂ ≫ F₁.map s ≫ epsilon₁ = epsilon₂)
    (tau₁ : H₁.obj K₁ ⟶ L) (tau₂ : H₂.obj K₂ ⟶ L)
    (h₁ : V.map tau₁ = alpha₁.app K₁ ≫ F₁.map e₁ ≫ epsilon₁)
    (h₂ : V.map tau₂ = alpha₂.app K₂ ≫ F₂.map e₂ ≫ epsilon₂) :
    V.map (p.app K₂ ≫ H₁.map a ≫ tau₁) = V.map tau₂ := by
  simp only [Functor.map_comp, h₁, h₂]
  have hn := alpha₁.naturality a
  dsimp only [Functor.comp_map] at hn
  rw [reassoc_of% hn]
  change V.map (p.app K₂) ≫ alpha₁.app K₂ ≫ F₁.map (R.map a) ≫
    F₁.map e₁ ≫ epsilon₁ = _
  rw [← Category.assoc, hp]
  simp only [Category.assoc]
  rw [← F₁.map_comp_assoc, he, F₁.map_comp]
  simp only [Category.assoc]
  rw [← t.naturality_assoc]
  rw [hs]


private theorem system_trace_square
    {A B : Type*} [Category A] [Category B]
    (F₁ F₂ : A ⥤ B) (t : F₂ ⟶ F₁)
    {M₁ M₂ N₁ N₂ : A} {L : B}
    (theta₁ : M₁ ⟶ N₁) (theta₂ : M₂ ⟶ N₂) (s : M₂ ⟶ M₁)
    (m : N₂ ⟶ N₁) (epsilon₁ : F₁.obj N₁ ⟶ L) (epsilon₂ : F₂.obj N₂ ⟶ L)
    (q : F₁.obj N₂ ⟶ F₂.obj N₂)
    (hs : s ≫ theta₁ = theta₂ ≫ m)
    (hm : F₁.map m ≫ epsilon₁ = q ≫ epsilon₂)
    (hq : t.app N₂ ≫ q = 𝟙 _) :
    t.app M₂ ≫ F₁.map s ≫ F₁.map theta₁ ≫ epsilon₁ =
      F₂.map theta₂ ≫ epsilon₂ := by
  rw [← F₁.map_comp_assoc, hs, F₁.map_comp]
  simp only [Category.assoc]
  rw [hm, ← t.naturality_assoc, ← Category.assoc (t.app N₂), hq, Category.id_comp]

end Abstract

attribute [local irreducible] coordinates purCoefficientModel
  PurIntegralSupportComparison.beta systemDown
  PurIntegralRepresentingPair.totalLimit
  PurIntegralRepresentingPair.adjunction PurIntegralRepresentingPair.supportPresentation
  CompactSupportCondensedRealization.alpha integralSupport integralRefinement
  systemRefinement

variable (l : ℕ) [Fact l.Prime] (E : Type u) [NormedField E]
  [NormedAlgebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]
  (C : ComparisonFamily l k)
  (X Y : CondensedERealization.Base k) (f : X.scheme ⟶ Y.scheme)
  [f.IsOver (Spec (.of k))]

/-- Reconstruction of the system counit square for supplied representing pairs.
Source: blueprint sk-prop-sp-unique-adjoint categorical proof, Transposes and
Uniqueness; parent proof Steps 4--5.
Proof: let e_i be the actual reduction/limit counit on the supplied systems.
Naturality gives R(sbar) followed by e_1 equal to e_2 followed by s.
The Brown Hom formula and the definition of mate give its counit equation.
Apply compact support to the supplied theta square, use that equation and
naturality of the constructed system comparison. Insert these identities in
PublishedFamily.trace_reduction for both traces, along with naturality of alpha
and its actual refinement square. The two reductions of the desired integral
maps now agree. Reduction on derived-complete objects is fully faithful by the
normalized reconstruction adjunction; hence the integral maps agree. Coordinate
equivalence preserves this calculation, including its counit factors.
This private compatibility lemma preserves the existing legacy consumer only. -/
private theorem legacyRefinementTraceSquare :
    ∀ (c d : Compactification f)
    (D₁ : At l E k C X Y f c) (D₂ : At l E k C X Y f d) (w : c.Refinement d)
    (L : CondensedERealization.Integral l E Y.scheme)
    (A₁ : D₁.Supplied L) (A₂ : D₂.Supplied L) (s : A₂.system ≅ A₁.system),
    s.hom ≫ (D₁.pair L A₁).theta.hom =
      (D₂.pair L A₂).theta.hom ≫ mate D₁ D₂ w L A₁ A₂ →
    (support l E k C X Y f c).map (reconstructedMap D₁ D₂ L A₁ A₂ s.hom) ≫
      D₁.trace L A₁ =
        (comparison l E k C X Y f w).hom.app A₂.object ≫ D₂.trace L A₂ := by
  intro c d D₁ D₂ w L A₁ A₂ s hs
  let rx := (C.coefficient E).reduction X.scheme
  let ry := (C.coefficient E).reduction Y.scheme
  let RX := integralReduction l E k X rx ⋙ (coordinates l E X.scheme).functor
  let RY := integralReduction l E k Y ry ⋙ (coordinates l E Y.scheme).functor
  let F₁ := D₁.transport.compact.functor
  let F₂ := D₂.transport.compact.functor
  let H₁ := support l E k C X Y f c
  let H₂ := support l E k C X Y f d
  let b₁ := beta l E D₁.strict D₁.brown D₁.finite D₁.transport
  let b₂ := beta l E D₂.strict D₂.brown D₂.finite D₂.transport
  let a₁ : H₁ ⋙ integralReduction l E k Y ry ⟶
      integralReduction l E k X rx ⋙ systemSupport l E c := by
    simpa only [H₁, support, integralReduction, reconstructedSystem, rx, ry, Functor.assoc] using
      (alpha l E c (C.coefficient E).reduction
        ((C.coefficient E).atCompactification X Y f c).integral)
  let a₂ : H₂ ⋙ integralReduction l E k Y ry ⟶
      integralReduction l E k X rx ⋙ systemSupport l E d := by
    simpa only [H₂, support, integralReduction, reconstructedSystem, rx, ry, Functor.assoc] using
      (alpha l E d (C.coefficient E).reduction
        ((C.coefficient E).atCompactification X Y f d).integral)
  let alpha₁ : H₁ ⋙ RY ⟶ RX ⋙ F₁ :=
    Functor.whiskerRight a₁ (coordinates l E Y.scheme).functor ≫
      Functor.whiskerLeft (integralReduction l E k X rx) b₁.inv
  let alpha₂ : H₂ ⋙ RY ⟶ RX ⋙ F₂ :=
    Functor.whiskerRight a₂ (coordinates l E Y.scheme).functor ≫
      Functor.whiskerLeft (integralReduction l E k X rx) b₂.inv
  let p := integralRefinement l E k (C.coefficient E) X Y f w
  let t := systemDown D₁ D₂ w
  let a := reconstructedMap D₁ D₂ L A₁ A₂ s.hom
  have hp : RY.map (p.app A₂.object) ≫ alpha₁.app A₂.object =
      alpha₂.app A₂.object ≫ t.app (RX.obj A₂.object) := by
    let v := (coordinates l E Y.scheme).functor
    let K := (integralReduction l E k X rx).obj A₂.object
    have hc := (C.refinement E X Y f w).reduction A₂.object
    change (integralReduction l E k Y ry).map (p.app A₂.object) ≫
      a₁.app A₂.object = a₂.app A₂.object ≫
        (systemRefinement l E k X Y f w).app K at hc
    have hb := conjugate_on_image (coordinates l E X.scheme) v F₂ F₁
      (systemSupport l E d) (systemSupport l E c) b₂ b₁
      (systemRefinement l E k X Y f w) K
    have hb' : b₂.inv.app K ≫ t.app (RX.obj A₂.object) =
        v.map ((systemRefinement l E k X Y f w).app K) ≫ b₁.inv.app K := by
      dsimp only [RX, Functor.comp_obj, K, t, v, F₁, F₂, b₁, b₂] at hb ⊢
      unfold systemDown
      exact hb
    change v.map ((integralReduction l E k Y ry).map (p.app A₂.object)) ≫
      (v.map (a₁.app A₂.object) ≫ b₁.inv.app K) =
      (v.map (a₂.app A₂.object) ≫ b₂.inv.app K) ≫ t.app (RX.obj A₂.object)
    rw [← v.map_comp_assoc, hc, v.map_comp]
    simp only [Category.assoc]
    rw [hb']
  have he : RX.map a ≫
      (PurIntegralRepresentingPair.adjunction l E X.scheme rx).counit.app A₁.system =
      (PurIntegralRepresentingPair.adjunction l E X.scheme rx).counit.app A₂.system ≫
        s.hom := by
    exact (PurIntegralRepresentingPair.adjunction l E X.scheme rx).counit.naturality s.hom
  have hs' : t.app A₂.system ≫
      F₁.map s.hom ≫ F₁.map (D₁.pair L A₁).theta.hom ≫ D₁.counit L A₁ =
      F₂.map (D₂.pair L A₂).theta.hom ≫ D₂.counit L A₂ := by
    have := D₁.transport.finite
    have hm := (D₁.transport.hom _ (D₁.pair L A₁).origin (D₁.pair L A₁).normalized
      (D₁.pair L A₁).finiteTor (D₁.pair L A₁).lowerBound _
      (output_origin D₁ D₂ L A₂)).apply_symm_apply
      ((systemComparison D₁ D₂ w (D₂.output L) (output_origin D₁ D₂ L A₂)).hom ≫
        D₂.counit L A₂)
    have hm' : F₁.map (mate D₁ D₂ w L A₁ A₂) ≫ D₁.counit L A₁ =
        (systemComparison D₁ D₂ w (D₂.output L)
          (output_origin D₁ D₂ L A₂)).hom ≫ D₂.counit L A₂ := by
      calc
        _ = (D₁.transport.hom _ (D₁.pair L A₁).origin (D₁.pair L A₁).normalized
            (D₁.pair L A₁).finiteTor (D₁.pair L A₁).lowerBound _
            (output_origin D₁ D₂ L A₂)) (mate D₁ D₂ w L A₁ A₂) := by
          exact (D₁.normalized.hom_formula _ _ _ _ _ _ _ _).symm
        _ = _ := by simpa only [mate] using hm
    have hi : (systemDown D₁ D₂ w).app (D₂.output L) ≫
        (systemComparison D₁ D₂ w (D₂.output L) (output_origin D₁ D₂ L A₂)).hom =
        𝟙 _ := by
      have := systemDown_isIso D₁ D₂ w (D₂.output L) (output_origin D₁ D₂ L A₂)
      simpa only [systemComparison, Iso.symm_hom, asIso_inv] using
        IsIso.hom_inv_id ((systemDown D₁ D₂ w).app (D₂.output L))
    exact system_trace_square F₁ F₂ t (D₁.pair L A₁).theta.hom
      (D₂.pair L A₂).theta.hom s.hom (mate D₁ D₂ w L A₁ A₂)
      (D₁.counit L A₁) (D₂.counit L A₂) _ hs hm' hi
  have h₁ : RY.map (D₁.trace L A₁) = alpha₁.app A₁.object ≫
      F₁.map ((PurIntegralRepresentingPair.adjunction l E X.scheme rx).counit.app
        A₁.system) ≫ F₁.map (D₁.pair L A₁).theta.hom ≫ D₁.counit L A₁ := by
    dsimp only [alpha₁, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app]
    exact (D₁.pairs.trace_reduction L A₁).trans (Category.assoc _ _ _).symm
  have h₂ : RY.map (D₂.trace L A₂) = alpha₂.app A₂.object ≫
      F₂.map ((PurIntegralRepresentingPair.adjunction l E X.scheme rx).counit.app
        A₂.system) ≫ F₂.map (D₂.pair L A₂).theta.hom ≫ D₂.counit L A₂ := by
    dsimp only [alpha₂, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app]
    exact (D₂.pairs.trace_reduction L A₂).trans (Category.assoc _ _ _).symm
  have hred := trace_square_of_reduction RX RY F₁ F₂ H₁ H₂ alpha₁ alpha₂ p t
    A₁.object A₂.object a hp A₁.system A₂.system L s.hom _ _ he
    (F₁.map (D₁.pair L A₁).theta.hom ≫ D₁.counit L A₁)
    (F₂.map (D₂.pair L A₂).theta.hom ≫ D₂.counit L A₂)
    hs' (D₁.trace L A₁) (D₂.trace L A₂) h₁ h₂
  have ht : p.app A₂.object ≫ H₁.map a ≫ D₁.trace L A₁ = D₂.trace L A₂ := by
    apply ObjectProperty.hom_ext
    have := (D₁.pair L A₁).unit_iso
    apply adjunction_detects_maps
      (PurIntegralRepresentingPair.adjunction l E Y.scheme ry)
    exact hred
  have := (C.refinement E X Y f w).invertible
  apply (cancel_epi (p.app A₂.object)).1
  change p.app A₂.object ≫ (H₁.map a ≫ D₁.trace L A₁) = _
  rw [ht]
  simpa only [comparison, p, Iso.symm_hom, asIso_hom] using
    ((asIso p).hom_inv_id_app_assoc A₂.object (D₂.trace L A₂)).symm

end LegacyTraceCompatibility

attribute [local irreducible] systemRefinement integralRefinement
  comparison coordinates PurIntegralSupportComparison.beta reconstructedMap mate
  fieldSupport fieldComparison fieldTrace scalarTrace omegaSupport toOmega omegaComparison
  omegaTrace systemComparison systemDown systemCommon commonComparison
variable (l : ℕ) [Fact l.Prime] (E : Type u) [NormedField E]
  [NormedAlgebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]
  (C : ComparisonFamily l k)
  (X Y : CondensedERealization.Base k) (f : X.scheme ⟶ Y.scheme)
  [f.IsOver (Spec (.of k))]

private theorem conjugate_id
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    (e : A ≌ B) (v : C ⥤ D) (F : B ⥤ D) (F' : A ⥤ C)
    (a : e.functor ⋙ F ≅ F' ⋙ v) :
    conjugate e v F F F' F' a a (𝟙 F') = 𝟙 F := by
  ext K
  unfold conjugate conjugateComponent
  dsimp only [NatTrans.id_app]
  rw [v.map_id]
  dsimp only [CategoryTheory.Functor.comp_obj]
  rw [Category.id_comp]
  rw [a.hom_inv_id_app_assoc, ← F.map_comp,
    e.counitIso.inv_hom_id_app]
  dsimp only [CategoryTheory.Functor.id_obj]
  exact F.map_id K

private theorem conjugate_comp
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    (e : A ≌ B) (v : C ⥤ D) (F G H : B ⥤ D) (F' G' H' : A ⥤ C)
    (a : e.functor ⋙ F ≅ F' ⋙ v) (b : e.functor ⋙ G ≅ G' ⋙ v)
    (c : e.functor ⋙ H ≅ H' ⋙ v) (s : F' ⟶ G') (t : G' ⟶ H') :
    conjugate e v F H F' H' a c (s ≫ t) =
      conjugate e v F G F' G' a b s ≫ conjugate e v G H G' H' b c t := by
  ext K
  unfold conjugate conjugateComponent
  dsimp only [NatTrans.comp_app]
  rw [v.map_comp]
  simp only [Category.assoc]
  rw [← G.map_comp_assoc, Iso.hom_inv_id_app]
  dsimp only [CategoryTheory.Functor.comp_obj]
  rw [G.map_id]
  simp only [Category.id_comp, Iso.inv_hom_id_app_assoc]

private theorem integral_down_id (c : Compactification f) :
    integralRefinement l E k (C.coefficient E) X Y f
      (Compactification.Refinement.id c) = 𝟙 _ := by
  ext K
  unfold integralRefinement liftSupportTransformation rawRefinement
  dsimp only [Functor.whiskerLeft_app, Functor.whiskerRight_app, NatTrans.comp_app,
    ObjectProperty.FullSubcategory.comp_hom]
  change (coefficientSequenceDerivedRestriction l E Y.scheme ⋙
      coefficientConstantTowerLimit l E Y.scheme ⋙
      (purCoefficientModel l E Y.scheme).inverse).map
    ((systemRefinement l E k X Y f (Compactification.Refinement.id c)).app _) = 𝟙 _
  rw [systemRefinement_id, NatTrans.id_app, CategoryTheory.Functor.map_id]

private theorem integral_down_comp {c d e : Compactification f}
    (r : c.Refinement d) (s : d.Refinement e) :
    integralRefinement l E k (C.coefficient E) X Y f (r.comp s) =
      integralRefinement l E k (C.coefficient E) X Y f s ≫
        integralRefinement l E k (C.coefficient E) X Y f r := by
  ext K
  unfold integralRefinement liftSupportTransformation rawRefinement
  dsimp only [Functor.whiskerLeft_app, Functor.whiskerRight_app, NatTrans.comp_app,
    ObjectProperty.FullSubcategory.comp_hom]
  change (coefficientSequenceDerivedRestriction l E Y.scheme ⋙
      coefficientConstantTowerLimit l E Y.scheme ⋙
      (purCoefficientModel l E Y.scheme).inverse).map
      ((systemRefinement l E k X Y f (r.comp s)).app _) =
    (coefficientSequenceDerivedRestriction l E Y.scheme ⋙
      coefficientConstantTowerLimit l E Y.scheme ⋙
      (purCoefficientModel l E Y.scheme).inverse).map
      ((systemRefinement l E k X Y f s).app _) ≫
    (coefficientSequenceDerivedRestriction l E Y.scheme ⋙
      coefficientConstantTowerLimit l E Y.scheme ⋙
      (purCoefficientModel l E Y.scheme).inverse).map
      ((systemRefinement l E k X Y f r).app _)
  rw [systemRefinement_comp, NatTrans.comp_app, Functor.map_comp]

private theorem common_trace
    {A B : Type*} [Category A] [Category B] (F₀ F₁ F₂ : A ⥤ B)
    (q₁ : F₀ ≅ F₁) (q₂ : F₀ ≅ F₂) {M₀ M₁ M₂ : A} {L : B}
    (a₁ : M₁ ⟶ M₀) (a₂ : M₂ ⟶ M₀) (b₁ : M₀ ⟶ M₁)
    (t₀ : F₀.obj M₀ ⟶ L) (t₁ : F₁.obj M₁ ⟶ L) (t₂ : F₂.obj M₂ ⟶ L)
    (hb : b₁ ≫ a₁ = 𝟙 _) (h₁ : F₀.map a₁ ≫ t₀ = q₁.hom.app M₁ ≫ t₁)
    (h₂ : F₀.map a₂ ≫ t₀ = q₂.hom.app M₂ ≫ t₂) :
    F₁.map (a₂ ≫ b₁) ≫ t₁ = (q₁.symm ≪≫ q₂).hom.app M₂ ≫ t₂ := by
  apply (cancel_epi (q₁.hom.app M₂)).1
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc,
    Iso.hom_inv_id_app_assoc]
  rw [← q₁.hom.naturality_assoc, Functor.map_comp, Category.assoc,
    ← h₁, ← F₀.map_comp_assoc b₁ a₁, hb, F₀.map_id, Category.id_comp]
  exact h₂

private theorem cancel_iso_hom
    {A : Type*} [Category A] {X Y Z : A} (q : X ≅ Y) {a b : Y ⟶ Z}
    (h : q.hom ≫ a = q.hom ≫ b) : a = b :=
  (cancel_epi q.hom).1 h

private theorem inverse_square
    {A B : Type*} [Category A] [Category B] (R : A ⥤ B)
    {X Y : A} {Z : B} (q : X ≅ Y) (a : R.obj Y ⟶ Z) (b : R.obj X ⟶ Z)
    (h : R.map q.hom ≫ a = b) : R.map q.inv ≫ b = a := by
  rw [← h, ← R.map_comp_assoc, q.inv_hom_id, R.map_id, Category.id_comp]

private theorem transpose_square
    {A B : Type*} [Category A] [Category B] (F G : A ⥤ B)
    (J₁ J₂ : B ⥤ A) (adj₁ : F ⊣ J₁) (adj₂ : G ⊣ J₂) (q : F ≅ G)
    {M₁ M₂ : A} {L : B} (a : M₂ ⟶ M₁)
    (t₁ : F.obj M₁ ⟶ L) (t₂ : G.obj M₂ ⟶ L)
    (h : F.map a ≫ t₁ = q.hom.app M₂ ≫ t₂) :
    a ≫ adj₁.homEquiv _ _ t₁ = adj₂.homEquiv _ _ t₂ ≫
      (conjugateEquiv adj₂ adj₁ q.hom).app L := by
  apply (adj₁.homEquiv _ _).symm.injective
  rw [adj₁.homEquiv_naturality_left_symm, Equiv.symm_apply_apply]
  rw [Adjunction.homEquiv_counit, F.map_comp, Category.assoc,
    conjugateEquiv_counit, ← Category.assoc, q.hom.naturality, Category.assoc,
    ← adj₂.homEquiv_counit, Equiv.symm_apply_apply]
  exact h

/-- Reconstructed representing pairs respect the canonical proper refinement and its
counit-preserving mate, before and after coefficient realization.
Source: current blueprint sk-prop-sp-unique-adjoint categorical proof, Transposes,
Naturality and Uniqueness; sk-thm-purity-transport Steps 2--4
(blueprint: lem-pur-reconstructed-pair-refinement-coherence).

Proof (the node's eight steps):
1. The ringed-system open-adjoint clopen projection and the proper compositor define
systemRefinement. The section-normalized beta transports it to systemDown. Its
finite evaluations are the normalized constant-coefficient comparisons. Finite
proper/open calculus and conservative evaluations establish invertibility on the
bounded-below etale-origin domain, so systemComparison has the specified direction.
2. Varying-ring proper/open pasting gives d_vw = d_v d_w and d_id = id as system
maps; invert them on the stated domain. Common-refinement independence follows by
cancelling the same further-refinement factor. Cofilteredness supplies common
dominators and equalizers of parallel arrows. Cancellation gives the cocycle.
3. Normalized reconstruction identifies the actual reduction/limit unit and counit
with isomorphisms on complete objects. Faithfulness of reduction identifies the
reconstructed q with comparison and gives the displayed alpha square. It also
carries the system identity, composition and common-refinement laws to the integral
category. The coordinate equivalence does not change any underlying map.
4. The actual Brown Hom inverse defines mate. Its Hom formula gives mate_counit;
naturality, the supplied theta square and naturality of systemComparison give
F1(s) followed by the first supplied counit equal to q followed by the second.
For the single-degree alternative use the normalized good truncation and the fully
faithful shifted heart; exact conservative evaluations detect equality of the
resulting heart maps, never arbitrary derived-system maps.
5. Naturality of the actual reduction/limit counit gives e1 R(sbar) = s e2.
Insert this, the system counit identity of Step 4, naturality of q and the actual
alpha square into the published trace_reduction formulas. Both reductions of the
integral counit equation coincide. Faithfulness of reduction on complete objects
proves counit in Equations.
6. Naturality of the published representing bijections gives B(h) = P(h) followed
by the trace. Substitute Step 5 and use naturality of comparison to obtain hom.
Mates reverse composition, giving mate_comp; invertible theta then gives the
corresponding composition of supplied maps, and total limit preserves it. The
common-refinement and cocycle formulas prove independence of every such equation.
7. Apply actual completed integral scalar extension to Step 5 and insert the
specified compact-support tensor comparisons. Their refinement square gives scalar.
Their tensor associators give scalar_transitive, also when tS = v^eS: use cofinal
levels and actual system isomorphisms, without concentration after nonflat quotients.
8. Rationalize Step 5 and apply the specified E realization comparison, obtaining
field. Apply finite-valued closure scalar extension and its compact-support
projection comparison, obtaining omega. Common finite fields of definition for
objects and finite morphism diagrams, and Step 7 transitivity, make the equation
independent of presentation. For specified closure right adjoints, transpose the
two maps using the first Hom bijection. The first transpose is t1 P1(sOmega);
the conjugate-mate counit formula and naturality make the second t2 qOmega.
They agree by omega, and injectivity proves transpose. All operations preserve
composition, so the same proof retains successive/common refinement and coefficient
compatibility. -/
theorem reconstructedPairRefinementCoherence : Coherence l E k C X Y f := by
  have hsid (c : Compactification f) (D : At l E k C X Y f c) :
      systemDown D D (Compactification.Refinement.id c) = 𝟙 _ := by
    unfold systemDown
    rw [systemRefinement_id]
    exact conjugate_id _ _ _ _ _
  have hscomp (c d e : Compactification f)
      (D₁ : At l E k C X Y f c) (D₂ : At l E k C X Y f d)
      (D₃ : At l E k C X Y f e) (r : c.Refinement d) (s : d.Refinement e) :
      systemDown D₁ D₃ (r.comp s) = systemDown D₂ D₃ s ≫ systemDown D₁ D₂ r := by
    unfold systemDown
    rw [systemRefinement_comp]
    exact conjugate_comp _ _ _ _ _ _ _ _ _ _ _ _ _
  have hid (c : Compactification f) :
      comparison l E k C X Y f (Compactification.Refinement.id c) = Iso.refl _ := by
    apply Iso.ext_inv
    unfold comparison
    dsimp only [Iso.symm_inv, asIso_hom, Iso.trans_inv]
    change integralRefinement l E k (C.coefficient E) X Y f
      (Compactification.Refinement.id c) = 𝟙 _
    exact integral_down_id l E k C X Y f c
  have hcomp (c d e : Compactification f) (r : c.Refinement d) (s : d.Refinement e) :
      comparison l E k C X Y f (r.comp s) =
        comparison l E k C X Y f r ≪≫ comparison l E k C X Y f s := by
    apply Iso.ext_inv
    unfold comparison
    dsimp only [Iso.symm_inv, asIso_hom, Iso.trans_inv]
    change integralRefinement l E k (C.coefficient E) X Y f (r.comp s) = _
    exact integral_down_comp l E k C X Y f r s
  refine {
    system_id := hsid
    system_comp := hscomp
    system_common_independent := ?_
    system_cocycle := ?_
    integral_id := hid
    integral_comp := hcomp
    common_independent := ?_
    cocycle := ?_
    reduction := ?_
    mate_counit := ?_
    mate_iso := ?_
    mate_comp := ?_
    pairs := ?_
    single_degree := ?_
    common_pair_counit := ?_
    scalar_identity := ?_
    scalar_transitive := ?_ }
  · exact (reconstructedRefinementCommon l E k C X Y f).1
  · intro c d e h D₁ D₂ D₃ D₀ r₁ r₂ r₃ B hB
    apply Iso.ext
    simp only [systemCommon, Iso.trans_hom, Iso.symm_hom, Category.assoc,
      Iso.hom_inv_id_assoc]
  · exact (reconstructedRefinementCommon l E k C X Y f).2
  · intro c d e a b h r₁ r₂ s₂ s₃ t₁ t₃
    have hc := (reconstructedRefinementCommon l E k C X Y f).2
    obtain ⟨z, ⟨u⟩, ⟨v⟩⟩ := Compactification.exists_common_refinement c d
    obtain ⟨z', ⟨u'⟩, ⟨v'⟩⟩ := Compactification.exists_common_refinement z e
    let p₁ := u'.comp u
    let p₂ := u'.comp v
    rw [hc c d a z' r₁ r₂ p₁ p₂, hc d e b z' s₂ s₃ p₂ v',
      hc c e h z' t₁ t₃ p₁ v']
    apply Iso.ext
    simp only [commonComparison, Iso.trans_hom, Iso.symm_hom, Category.assoc,
      Iso.hom_inv_id_assoc]
  · intro c d w K
    have := (C.refinement E X Y f w).invertible
    have ht := (C.refinement E X Y f w).reduction K
    have he := inverse_square
      (integralReduction l E k Y ((C.coefficient E).reduction Y.scheme))
      ((asIso (integralRefinement l E k (C.coefficient E) X Y f w)).app K)
      ((alpha l E c (C.coefficient E).reduction
        ((C.coefficient E).atCompactification X Y f c).integral).app K)
      ((alpha l E d (C.coefficient E).reduction
        ((C.coefficient E).atCompactification X Y f d).integral).app K ≫
        (systemRefinement l E k X Y f w).app
          ((integralReduction l E k X ((C.coefficient E).reduction X.scheme)).obj K))
      (by simpa only [Iso.app_hom, asIso_hom] using ht)
    simpa only [comparison, Iso.symm_hom, Iso.app_inv, Category.assoc] using he
  · intro c d D₁ D₂ w L A₁ A₂
    have := D₁.transport.finite
    have he := (D₁.transport.hom _ (D₁.pair L A₁).origin (D₁.pair L A₁).normalized
      (D₁.pair L A₁).finiteTor (D₁.pair L A₁).lowerBound _
      (output_origin D₁ D₂ L A₂)).apply_symm_apply
      ((systemComparison D₁ D₂ w (D₂.output L) (output_origin D₁ D₂ L A₂)).hom ≫
        D₂.counit L A₂)
    rw [D₁.normalized.hom_formula] at he
    simpa only [mate, At.counit] using he
  · exact (reconstructedBrownMateLaws l E k C X Y f).1
  · exact (reconstructedBrownMateLaws l E k C X Y f).2
  · intro c d D₁ D₂ w L A₁ A₂ s hs
    have ht := legacyRefinementTraceSquare l E k C X Y f
      c d D₁ D₂ w L A₁ A₂ s hs
    obtain ⟨hscalar, hfield, homega⟩ :=
      reconstructedRefinementTraceTransport l E k C X Y f w A₁.object A₂.object L
        (reconstructedMap D₁ D₂ L A₁ A₂ s.hom) (D₁.trace L A₁) (D₂.trace L A₂) ht
    refine {
      counit := ht
      hom := ?_
      scalar := hscalar
      field := hfield
      field_hom := ?_
      omega := homega
      omega_hom := ?_
      transpose := ?_ }
    · intro K h
      have formula (D : At l E k C X Y f c) (A : D.Supplied L)
          (a : K ⟶ A.object) :
          D.pairs.hom L A K a = (support l E k C X Y f c).map a ≫ D.trace L A := by
        simpa only [Category.comp_id, At.trace] using
          D.pairs.hom_natural L A A.object K a (𝟙 A.object)
      have formula₂ : D₂.pairs.hom L A₂ K h =
          (support l E k C X Y f d).map h ≫ D₂.trace L A₂ := by
        simpa only [Category.comp_id, At.trace] using
          D₂.pairs.hom_natural L A₂ A₂.object K h (𝟙 A₂.object)
      rw [formula, formula₂, Functor.map_comp, Category.assoc, ht,
        ← Category.assoc, (comparison l E k C X Y f w).hom.naturality, Category.assoc]
    · intro K h
      rw [Functor.map_comp, Category.assoc, hfield, ← Category.assoc,
        (fieldComparison l E k C X Y f w).hom.naturality, Category.assoc]
    · intro a K h
      rw [Functor.map_comp, Category.assoc, homega, ← Category.assoc,
        (omegaComparison l k X Y f w).hom.naturality, Category.assoc]
    · intro a J₁ J₂ adj₁ adj₂
      exact transpose_square _ _ J₁ J₂ adj₁ adj₂ (omegaComparison l k X Y f w)
        _ _ _ (homega a)
  · exact reconstructedRefinementSingleDegree l E k C X Y f
  · intro c d e D₁ D₂ D₀ r s L A₁ A₂ A₀ s₁ s₂ hs₁ hs₂
    have h₁ := legacyRefinementTraceSquare l E k C X Y f
      e c D₀ D₁ r L A₀ A₁ s₁ hs₁
    have h₂ := legacyRefinementTraceSquare l E k C X Y f
      e d D₀ D₂ s L A₀ A₂ s₂ hs₂
    let a₁ := reconstructedMap D₀ D₁ L A₀ A₁ s₁.hom
    let a₂ := reconstructedMap D₀ D₂ L A₀ A₂ s₂.hom
    let b₁ := reconstructedMap D₁ D₀ L A₁ A₀ s₁.inv
    have hab : b₁ ≫ a₁ = 𝟙 _ := by
      apply ObjectProperty.hom_ext
      dsimp only [a₁, b₁]
      unfold reconstructedMap
      change (PurIntegralRepresentingPair.totalLimit l E X.scheme).map s₁.inv ≫
        (PurIntegralRepresentingPair.totalLimit l E X.scheme).map s₁.hom = 𝟙 _
      rw [← Functor.map_comp, s₁.inv_hom_id, CategoryTheory.Functor.map_id]
    have hmap : reconstructedMap D₁ D₂ L A₁ A₂ (s₂ ≪≫ s₁.symm).hom = a₂ ≫ b₁ := by
      apply ObjectProperty.hom_ext
      dsimp only [a₂, b₁]
      unfold reconstructedMap
      exact (PurIntegralRepresentingPair.totalLimit l E X.scheme).map_comp _ _
    rw [hmap]
    unfold commonComparison
    exact common_trace _ _ _ (comparison l E k C X Y f r)
      (comparison l E k C X Y f s) a₁ a₂ b₁
      (D₀.trace L A₀) (D₁.trace L A₁) (D₂.trace L A₂) hab h₁ h₂
  · intro c M L t
    unfold scalarTrace
    have hc := C.scalar_identity E X Y f c M
    have hn := (integralScalarId l E k Y).hom.naturality t
    apply (cancel_epi ((C.finite E E (AlgHom.id ℚ_[l] E) X Y f c).comparison.hom.app M)).1
    simp only [Category.assoc]
    rw [← Category.assoc, hc]
    simp only [Iso.hom_inv_id_app_assoc]
    exact hn.symm
  · intro H H' _ _ _ _ _ _ i j c M L t
    unfold scalarTrace
    have hc := C.scalar_composition E H H' i j X Y f c M
    have hn := (integralScalarComp l E H H' i j k Y).hom.naturality t
    let q := (integralScalar l H H' j k Y).mapIso
      ((C.finite E H i X Y f c).comparison.app M) ≪≫
        (C.finite H H' j X Y f c).comparison.app
          ((integralScalar l E H i k X).obj M)
    apply cancel_iso_hom q
    dsimp only [q, Iso.trans_hom, CategoryTheory.Functor.mapIso_hom, Iso.app_hom]
    simp only [Category.assoc, Functor.map_comp]
    have hc' := congrArg (fun z ↦ z ≫
      (C.finite E H' (j.comp i) X Y f c).comparison.inv.app M ≫
        (integralScalar l E H' (j.comp i) k Y).map t) hc
    simp only [Category.assoc, Iso.hom_inv_id_app_assoc] at hc'
    rw [hc']
    simp only [Iso.hom_inv_id_app_assoc, ← Functor.map_comp_assoc]
    exact hn.symm

end WeilConjectures.ReconstructedPairRefinement
