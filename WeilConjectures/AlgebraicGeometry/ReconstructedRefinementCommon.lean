/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ReconstructedPairRefinementData
import WeilConjectures.AlgebraicGeometry.RefinementFiniteOriginEvaluation
import WeilConjectures.Compactification.Cofiltered

/-! # Reconstructed RefinementCommon

Source: blueprint sk-prop-sp-unique-adjoint, categorical proof, and
sk-thm-purity-transport Steps 2--4
(blueprint: lem-pur-reconstructed-refinement-common).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
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
private theorem refinement_comp {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d e : Compactification f} (r : c.Refinement d) (s : d.Refinement e) :
    @CategoryStruct.comp (Compactification f) _ c d e r s = r.comp s := by
  rfl

variable (l : ℕ) [Fact l.Prime] (E : Type u) [NormedField E]
  [NormedAlgebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]
  (C : ComparisonFamily l k)
  (X Y : CondensedERealization.Base k) (f : X.scheme ⟶ Y.scheme)
  [f.IsOver (Spec (.of k))]

private theorem common_ratio
    {J A : Type*} [Category J] [IsCofilteredOrEmpty J] [Category A]
    (F : J → A) (q : ∀ {i j : J}, (i ⟶ j) → (F j ≅ F i))
    (hcomp : ∀ {i j h : J} (r : i ⟶ j) (s : j ⟶ h),
      q (r ≫ s) = q s ≪≫ q r)
    {c d e e' : J} (r : e ⟶ c) (s : e ⟶ d) (r' : e' ⟶ c) (s' : e' ⟶ d) :
    q r ≪≫ (q s).symm = q r' ≪≫ (q s').symm := by
  have refine_ratio {a b c d : J} (t : a ⟶ b) (r : b ⟶ c) (s : b ⟶ d) :
      q (t ≫ r) ≪≫ (q (t ≫ s)).symm = q r ≪≫ (q s).symm := by
    rw [hcomp, hcomp]
    apply Iso.ext
    simp only [Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, Category.assoc,
      Iso.hom_inv_id_assoc]
  obtain ⟨z, t, v, hr, hs⟩ := IsCofiltered.bowtie r r' s s'
  rw [← refine_ratio t r s, ← refine_ratio v r' s', hr, hs]

private theorem conjugated_ratio
    {A B : Type*} [Category A] [Category B] (v : A ⥤ B)
    {X₀ X₁ X₂ : B} {Y₀ Y₁ Y₂ : A}
    (a₀ : X₀ ≅ v.obj Y₀) (a₁ : X₁ ≅ v.obj Y₁) (a₂ : X₂ ≅ v.obj Y₂)
    (r : Y₁ ≅ Y₀) (s : Y₂ ≅ Y₀) :
    (a₁ ≪≫ v.mapIso r ≪≫ a₀.symm) ≪≫
        (a₂ ≪≫ v.mapIso s ≪≫ a₀.symm).symm =
      a₁ ≪≫ v.mapIso (r ≪≫ s.symm) ≪≫ a₂.symm := by
  apply Iso.ext
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.symm_inv, Iso.trans_inv, Functor.mapIso_hom,
    Functor.mapIso_inv, Functor.map_comp, Category.assoc, Iso.inv_hom_id_assoc]

private theorem conjugated_span_independence
    {J A B : Type*} [Category J] [IsCofilteredOrEmpty J] [Category A] [Category B]
    (F : J → A) (t : ∀ {i j : J}, (i ⟶ j) → (F j ⟶ F i))
    (hi : ∀ {i j : J} (r : i ⟶ j), IsIso (t r))
    (hcomp : ∀ {i j h : J} (r : i ⟶ j) (s : j ⟶ h), t (r ≫ s) = t s ≫ t r)
    (V : A ⥤ B) {c d e e' : J}
    (r : e ⟶ c) (s : e ⟶ d) (r' : e' ⟶ c) (s' : e' ⟶ d)
    {P Q R R' : B}
    (aP : P ≅ V.obj (F c)) (aQ : Q ≅ V.obj (F d))
    (aR : R ≅ V.obj (F e)) (aR' : R' ≅ V.obj (F e'))
    (u : P ≅ R) (v : Q ≅ R) (u' : P ≅ R') (v' : Q ≅ R')
    (hu : u.hom = aP.hom ≫ V.map (t r) ≫ aR.inv)
    (hv : v.hom = aQ.hom ≫ V.map (t s) ≫ aR.inv)
    (hu' : u'.hom = aP.hom ≫ V.map (t r') ≫ aR'.inv)
    (hv' : v'.hom = aQ.hom ≫ V.map (t s') ≫ aR'.inv) :
    u ≪≫ v.symm = u' ≪≫ v'.symm := by
  let q {i j : J} (a : i ⟶ j) := @asIso _ _ _ _ (t a) (hi a)
  have hq {i j h : J} (a : i ⟶ j) (b : j ⟶ h) :
      q (a ≫ b) = q b ≪≫ q a := by
    apply Iso.ext
    exact hcomp a b
  have hc := common_ratio F @q @hq r s r' s'
  have hu₀ : u = aP ≪≫ V.mapIso (q r) ≪≫ aR.symm := Iso.ext hu
  have hv₀ : v = aQ ≪≫ V.mapIso (q s) ≪≫ aR.symm := Iso.ext hv
  have hu₁ : u' = aP ≪≫ V.mapIso (q r') ≪≫ aR'.symm := Iso.ext hu'
  have hv₁ : v' = aQ ≪≫ V.mapIso (q s') ≪≫ aR'.symm := Iso.ext hv'
  rw [hu₀, hv₀, hu₁, hv₁, conjugated_ratio, conjugated_ratio, hc]

private theorem conjugated_refinement_spans
    {J A B C D : Type*} [Category J] [IsCofilteredOrEmpty J]
    [Category A] [Category B] [Category C] [Category D]
    (e : A ≌ B) (V : C ⥤ D) (F : J → (A ⥤ C))
    (t : ∀ {i j : J}, (i ⟶ j) → (F j ⟶ F i))
    (K : B)
    (hi : ∀ {i j : J} (r : i ⟶ j), IsIso ((t r).app (e.inverse.obj K)))
    (hcomp : ∀ {i j h : J} (r : i ⟶ j) (s : j ⟶ h),
      (t (r ≫ s)).app (e.inverse.obj K) =
        (t s).app (e.inverse.obj K) ≫ (t r).app (e.inverse.obj K))
    {c d z z' : J} (r : z ⟶ c) (s : z ⟶ d) (r' : z' ⟶ c) (s' : z' ⟶ d)
    (Gc Gd Gz Gz' : B ⥤ D)
    (ac : e.functor ⋙ Gc ≅ F c ⋙ V) (ad : e.functor ⋙ Gd ≅ F d ⋙ V)
    (az : e.functor ⋙ Gz ≅ F z ⋙ V) (az' : e.functor ⋙ Gz' ≅ F z' ⋙ V)
    (u : Gz.obj K ≅ Gc.obj K) (v : Gz.obj K ≅ Gd.obj K)
    (u' : Gz'.obj K ≅ Gc.obj K) (v' : Gz'.obj K ≅ Gd.obj K)
    (hu : u.inv = (conjugate e V Gc Gz (F c) (F z) ac az (t r)).app K)
    (hv : v.inv = (conjugate e V Gd Gz (F d) (F z) ad az (t s)).app K)
    (hu' : u'.inv = (conjugate e V Gc Gz' (F c) (F z') ac az' (t r')).app K)
    (hv' : v'.inv = (conjugate e V Gd Gz' (F d) (F z') ad az' (t s')).app K) :
    u.symm ≪≫ v = u'.symm ≪≫ v' := by
  let coord {j : J} (G : B ⥤ D) (a : e.functor ⋙ G ≅ F j ⋙ V) :=
    G.mapIso (e.counitIso.app K).symm ≪≫ a.app (e.inverse.obj K)
  have h := conjugated_span_independence
    (fun j ↦ (F j).obj (e.inverse.obj K))
    (fun {_ _} a ↦ (t a).app (e.inverse.obj K)) hi hcomp V r s r' s'
    (coord Gc ac) (coord Gd ad) (coord Gz az) (coord Gz' az') u.symm v.symm u'.symm v'.symm
    (by simpa only [conjugate, conjugateComponent, coord, Iso.trans_hom, Iso.trans_inv,
      Functor.mapIso_hom, Functor.mapIso_inv, Iso.symm_hom, Iso.symm_inv,
      Iso.app_hom, Iso.app_inv, Category.assoc] using hu)
    (by simpa only [conjugate, conjugateComponent, coord, Iso.trans_hom, Iso.trans_inv,
      Functor.mapIso_hom, Functor.mapIso_inv, Iso.symm_hom, Iso.symm_inv,
      Iso.app_hom, Iso.app_inv, Category.assoc] using hv)
    (by simpa only [conjugate, conjugateComponent, coord, Iso.trans_hom, Iso.trans_inv,
      Functor.mapIso_hom, Functor.mapIso_inv, Iso.symm_hom, Iso.symm_inv,
      Iso.app_hom, Iso.app_inv, Category.assoc] using hu')
    (by simpa only [conjugate, conjugateComponent, coord, Iso.trans_hom, Iso.trans_inv,
      Functor.mapIso_hom, Functor.mapIso_inv, Iso.symm_hom, Iso.symm_inv,
      Iso.app_hom, Iso.app_inv, Category.assoc] using hv')
  simpa only [Iso.symm_symm_eq] using h


set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
attribute [local irreducible] systemRefinement coordinates in
private theorem intrinsic_invertible
    {c₀ c d : Compactification f} (D : At l E k C X Y f c₀) (w : c.Refinement d)
    (B : DerivedCategory (BrownTowerComparison.ProSystem X.scheme
      (integralExceptionalIntegers l E) (integralExceptionalUniformizer l E)))
    (hB : D.transport.siteX.Origin B) :
    IsIso ((systemRefinement l E k X Y f w).app
      ((coordinates l E X.scheme).inverse.obj B)) := by
  apply (((C.coefficient E).reduction Y.scheme).isIso_iff_evaluations _).2
  intro n
  apply systemRefinementEvaluation_isIso l E k X Y f w D.strict.PX D.transport.siteX _ n
  obtain ⟨H, hH, ⟨e⟩⟩ := hB.2 n
  exact ⟨H, hH, ⟨e ≪≫ (D.transport.siteX.proEvaluation.evaluation n).mapIso
    ((coordinates l E X.scheme).counitIso.app B).symm⟩⟩

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
attribute [local irreducible] systemRefinement integralRefinement coordinates in
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

attribute [local irreducible] systemRefinement integralRefinement coordinates
  PurIntegralSupportComparison.beta systemComparison systemDown systemCommon commonComparison

variable {l E k C X Y f}

private theorem comparison_inv {c d : Compactification f}
    (D₁ : At l E k C X Y f c) (D₂ : At l E k C X Y f d) (w : c.Refinement d)
    (B : DerivedCategory (BrownTowerComparison.ProSystem X.scheme
      (integralExceptionalIntegers l E) (integralExceptionalUniformizer l E)))
    (h : D₁.transport.siteX.Origin B) :
    (systemComparison D₁ D₂ w B h).inv = (systemDown D₁ D₂ w).app B := by
  unfold systemComparison
  rfl

private theorem down_conjugate {c d : Compactification f}
    (D₁ : At l E k C X Y f c) (D₂ : At l E k C X Y f d) (w : c.Refinement d) :
    systemDown D₁ D₂ w =
      conjugate (coordinates l E X.scheme) (coordinates l E Y.scheme).functor
        D₂.transport.compact.functor D₁.transport.compact.functor
        (systemSupport l E d) (systemSupport l E c)
        (beta l E D₂.strict D₂.brown D₂.finite D₂.transport)
        (beta l E D₁.strict D₁.brown D₁.finite D₁.transport)
        (systemRefinement l E k X Y f w) := by
  unfold systemDown
  rfl

variable (l E k C X Y f)

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- Common-refinement independence in system and reconstructed integral coordinates.
Source: Stacks Tags 0ATU and 0F7C--0F7J; parent proof Steps 2--3.
Proof: take a further compactification dominating the two chosen common refinements,
and equalize the two parallel arrows to each endpoint. For intrinsic system support,
composition factors each refined downward arrow through the same further-refinement
arrow. Its component is invertible on the bounded-below etale-origin input by finite
proper/open calculus and conservative evaluations. Cancel that common factor to
identify the ratios. Coordinate conjugation cancels its intermediate beta and
coordinate counit factors, so the same equality holds for systemCommon even when
the Brown packages at the two dominating objects differ. Applying actual total limit
and restricting to complete objects gives integral commonComparison independence.
No equality is detected merely from finite evaluations.
(blueprint: lem-pur-reconstructed-refinement-common). -/
theorem reconstructedRefinementCommon :
    (∀ (c d e e' : Compactification f)
    (D₁ : At l E k C X Y f c) (D₂ : At l E k C X Y f d)
    (D₀ : At l E k C X Y f e) (D₀' : At l E k C X Y f e')
    (r : e.Refinement c) (s : e.Refinement d)
    (r' : e'.Refinement c) (s' : e'.Refinement d)
    (B : DerivedCategory (BrownTowerComparison.ProSystem X.scheme
      (integralExceptionalIntegers l E) (integralExceptionalUniformizer l E)))
    (hB : D₀.transport.siteX.Origin B) (hB' : D₀'.transport.siteX.Origin B),
    systemCommon D₁ D₂ D₀ r s B hB = systemCommon D₁ D₂ D₀' r' s' B hB') ∧
    (∀ (c d e e' : Compactification f)
    (r : e.Refinement c) (s : e.Refinement d)
    (r' : e'.Refinement c) (s' : e'.Refinement d),
    commonComparison l E k C X Y f r s = commonComparison l E k C X Y f r' s') := by
  constructor
  · intro c d e e' D₁ D₂ D₀ D₀' r s r' s' B hB hB'
    unfold systemCommon
    exact conjugated_refinement_spans (coordinates l E X.scheme)
      (coordinates l E Y.scheme).functor (fun a ↦ systemSupport l E a)
      (fun {_ _} w ↦ systemRefinement l E k X Y f w) B
      (fun {_ _} w ↦ intrinsic_invertible l E k C X Y f D₀ w B hB)
      (fun {_ _ _} t w ↦
        (congrArg (fun a ↦ (systemRefinement l E k X Y f a).app
          ((coordinates l E X.scheme).inverse.obj B)) (refinement_comp t w)).trans
          ((systemRefinement_comp_component l E k X Y f t w
            ((coordinates l E X.scheme).inverse.obj B)).trans
            (NatTrans.comp_app _ _ _))) r s r' s'
      D₁.transport.compact.functor D₂.transport.compact.functor
      D₀.transport.compact.functor D₀'.transport.compact.functor
      (beta l E D₁.strict D₁.brown D₁.finite D₁.transport)
      (beta l E D₂.strict D₂.brown D₂.finite D₂.transport)
      (beta l E D₀.strict D₀.brown D₀.finite D₀.transport)
      (beta l E D₀'.strict D₀'.brown D₀'.finite D₀'.transport)
      (systemComparison D₀ D₁ r B hB) (systemComparison D₀ D₂ s B hB)
      (systemComparison D₀' D₁ r' B hB') (systemComparison D₀' D₂ s' B hB')
      ((comparison_inv D₀ D₁ r B hB).trans
        (congrArg (fun t ↦ t.app B) (down_conjugate D₀ D₁ r)))
      ((comparison_inv D₀ D₂ s B hB).trans
        (congrArg (fun t ↦ t.app B) (down_conjugate D₀ D₂ s)))
      ((comparison_inv D₀' D₁ r' B hB').trans
        (congrArg (fun t ↦ t.app B) (down_conjugate D₀' D₁ r')))
      ((comparison_inv D₀' D₂ s' B hB').trans
        (congrArg (fun t ↦ t.app B) (down_conjugate D₀' D₂ s')))
  · intro c d e e' r s r' s'
    have hi {a b : Compactification f} (w : a.Refinement b) :
        IsIso (integralRefinement l E k (C.coefficient E) X Y f w) :=
      (C.refinement E X Y f w).invertible
    let q {a b : Compactification f} (w : a.Refinement b) :=
      @asIso _ _ _ _ (integralRefinement l E k (C.coefficient E) X Y f w) (hi w)
    have hcomp {a b h : Compactification f} (t : a.Refinement b) (w : b.Refinement h) :
        q (@CategoryStruct.comp (Compactification f) _ a b h t w) = q w ≪≫ q t := by
      rw [refinement_comp t w]
      apply Iso.ext
      exact integral_down_comp l E k C X Y f t w
    unfold commonComparison comparison
    exact common_ratio (fun a ↦ support l E k C X Y f a) @q @hcomp r s r' s'


end WeilConjectures.ReconstructedPairRefinement
