/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CompactSupportFiniteProjection.FiniteProjectionCompositionData
import all WeilConjectures.SixFunctors.CompactSupportFiniteProjection.FiniteProjectionIterationRealization
import WeilConjectures.SixFunctors.CompactSupportFiniteProjection.FinitePullbackCompositionRealization
import WeilConjectures.AlgebraicGeometry.AmbientProperOpen.PullbackEqualityTransport
import all WeilConjectures.SixFunctors.CompactSupportFiniteProjection.FiniteSupportOriginComparison
import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCompactSupportCompositor

/-! # Tensor endpoints of the finite binary support compositor

This normalization has no projection morphism in its statement.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

set_option maxRecDepth 2048

universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.AmbientProperOpen
open AlgebraicGeometry.ProEtale.CompactCompositionProjection

namespace WeilConjectures.CompactSupportFiniteProjection

attribute [local irreducible] fixedTensor
attribute [local implicit_reducible] fixedScalarTensorData realizedPullTargetIso
  realizedTriangleTargetIso binaryPullCast binaryTargetComparison
  binaryIterationTargetComparison

attribute [local irreducible] sfIntrinsicDerivedEquivalence
attribute [local irreducible] AlgebraicGeometry.ProEtale.derivedTensor
attribute [local irreducible] Functor.mapDerivedCategory Functor.rightDerivedFunctor
  Functor.leftDerivedFunctor
attribute [local irreducible] DerivedCategory instCategoryDerivedCategory
  HasDerivedCategory.ofIsGrothendieckAbelian
  HasDerivedCategory.ofHasKInjectiveResolutions

private theorem realize_triangle
    {A B : Type*} [Category A] [Category B] (R : A ≌ B)
    {x y : B} {a b : A} (e : x ≅ R.functor.obj a) (s : y ≅ R.functor.obj b)
    (p : x ⟶ y) (q : b ⟶ a)
    (h : R.inverse.map p ≫ R.inverse.map s.hom ≫ R.unitIso.inv.app b ≫ q =
      R.inverse.map e.hom ≫ R.unitIso.inv.app a) :
    p ≫ s.hom ≫ R.functor.map q = e.hom := by
  apply R.inverse.map_injective
  apply (cancel_mono (R.unitIso.inv.app a)).1
  simp only [Functor.map_comp, Category.assoc]
  have hn := R.unitIso.inv.naturality q
  dsimp only [Functor.comp_map, Functor.id_map] at hn
  rw [hn]
  exact h

private theorem realize_square_tail
    {A B : Type*} [Category A] [Category B] (R : A ≌ B)
    {x y : B} {a b c : A} (e : x ≅ R.functor.obj a) (s : y ≅ R.functor.obj b)
    (p : x ⟶ y) (d : b ⟶ c) (f : a ⟶ c)
    (h : R.inverse.map p ≫ R.inverse.map s.hom ≫ R.unitIso.inv.app b ≫ d =
      R.inverse.map e.hom ≫ R.unitIso.inv.app a ≫ f) :
    p ≫ s.hom ≫ R.functor.map d = e.hom ≫ R.functor.map f := by
  apply R.inverse.map_injective
  apply (cancel_mono (R.unitIso.inv.app c)).1
  simp only [Functor.map_comp, Category.assoc]
  have hd := R.unitIso.inv.naturality d
  have hf := R.unitIso.inv.naturality f
  dsimp only [Functor.comp_map, Functor.id_map] at hd hf
  rw [hd, hf]
  exact h

private theorem target_paste
    {A B C : Type*} [Category A] [Category B] [Category C]
    (R : B ⥤ C) (F G : A ⥤ B) (alpha : F ⟶ G)
    {x₀ x₁ x₂ x₃ : A} {b₀ b₁ b₂ : C}
    (e : x₀ ⟶ x₁) (d : x₁ ⟶ x₂) (t : x₂ ⟶ x₃) (z : x₀ ⟶ x₃)
    (a : b₀ ⟶ b₁) (v : b₁ ⟶ b₂)
    (s₀ : b₁ ⟶ R.obj (F.obj x₀)) (s₁ : b₂ ⟶ R.obj (F.obj x₁))
    (h₀ : b₀ ⟶ R.obj (G.obj x₀))
    (hs : a ≫ s₀ ≫ R.map (alpha.app x₀) = h₀)
    (hn : v ≫ s₁ = s₀ ≫ R.map (F.map e)) (hi : e ≫ d ≫ t = z) :
    a ≫ v ≫ s₁ ≫ R.map (F.map d) ≫ R.map (alpha.app x₂) ≫ R.map (G.map t) =
      h₀ ≫ R.map (G.map z) := by
  have ht := congrArg R.map (alpha.naturality (e ≫ d))
  simp only [Functor.map_comp] at ht
  rw [reassoc_of% hn]
  rw [reassoc_of% ht, reassoc_of% hs]
  rw [← R.map_comp, ← R.map_comp, ← G.map_comp, ← G.map_comp, hi]

private theorem tensor_transport
    {A B : Type*} [Category A] [Category B] (R : A ≌ B) (T : A ⥤ A)
    {a b c d e : A} (p : a ⟶ b) (r : b ⟶ c) (s : c ⟶ d)
    (q : a ⟶ e) (t : e ⟶ d) (h : p ≫ r ≫ s = q ≫ t) :
    R.inverse.map (R.functor.map (T.map p)) ≫ (R.unitIso.app (T.obj b)).inv ≫
      T.map r ≫ T.map s =
    (R.unitIso.app (T.obj a)).inv ≫ T.map q ≫ T.map t := by
  have hn := R.unitIso.inv.naturality (T.map p)
  dsimp only [Functor.comp_map, Functor.id_map] at hn
  simp only [Iso.app_inv]
  rw [reassoc_of% hn]
  simp only [← T.map_comp, h]

private theorem forward_of_inverse
    {A : Type*} [Category A] {a b c : A} (e : a ≅ b)
    (p : a ⟶ c) (q : b ⟶ c) (h : e.inv ≫ p = q) : e.hom ≫ q = p := by
  rw [← h, Iso.hom_inv_id_assoc]

private theorem tensorize_four
    {A B : Type*} [Category A] [Category B]
    (T : A ⥤ A ⥤ A) (R : A ⥤ B) (l : A)
    {a b c d e : A} (p : a ⟶ b) (q : b ⟶ c) (r : c ⟶ d) (s : d ⟶ e)
    (t : a ⟶ e) (h : p ≫ q ≫ r ≫ s = t) :
    R.map ((T.map p).app l) ≫ R.map ((T.map q).app l) ≫
      R.map ((T.map r).app l) ≫
      R.map ((Functor.uncurry.obj T).map (Prod.mkHom s (𝟙 l))) =
        R.map ((T.map t).app l) := by
  change R.map ((T.map p).app l) ≫ R.map ((T.map q).app l) ≫
    R.map ((T.map r).app l) ≫
    R.map ((T.map s).app l ≫ (T.obj e).map (𝟙 l)) = _
  rw [CategoryTheory.Functor.map_id, Category.comp_id]
  have h' := congrArg ((T.flip.obj l ⋙ R).map) h
  simpa only [Functor.comp_map, Functor.map_comp, Functor.flip_obj_map,
    NatTrans.comp_app] using h'

private theorem trianglePull_cancel
    {G₀ : Type*} [Category G₀] {geo : G₀ ⥤ Scheme.{u}} (c : Calculus G₀ geo)
    {X₀ V₀ W₀ Y₀ B₀ Z₀ : G₀}
    (j₀ : X₀ ⟶ V₀) (b₀ : V₀ ⟶ W₀) (q₀ : V₀ ⟶ Y₀)
    (p₀ : W₀ ⟶ B₀) (i₀ : Y₀ ⟶ B₀) (s₀ : B₀ ⟶ Z₀)
    (hb₀ : b₀ ≫ p₀ = q₀ ≫ i₀)
    (hfg : (j₀ ≫ q₀) ≫ (i₀ ≫ s₀) = (j₀ ≫ b₀) ≫ (p₀ ≫ s₀)) (L₀ : c.D Z₀) :
    (c.pComp (j₀ ≫ q₀) (i₀ ≫ s₀)).hom.app L₀ ≫
        (trianglePull c j₀ b₀ q₀ p₀ i₀ s₀ hb₀).hom.app L₀ =
      (morphismPullbackCongr c hfg).hom.app L₀ := by
  rw [morphismPullbackCongr_eq]
  simp only [trianglePull, Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom,
    Iso.hom_inv_id_app_assoc]

private theorem trianglePull_cancelIso
    {G₀ : Type*} [Category G₀] {geo : G₀ ⥤ Scheme.{u}} (c : Calculus G₀ geo)
    {X₀ V₀ W₀ Y₀ B₀ Z₀ : G₀}
    (j₀ : X₀ ⟶ V₀) (b₀ : V₀ ⟶ W₀) (q₀ : V₀ ⟶ Y₀)
    (p₀ : W₀ ⟶ B₀) (i₀ : Y₀ ⟶ B₀) (s₀ : B₀ ⟶ Z₀)
    (hb₀ : b₀ ≫ p₀ = q₀ ≫ i₀)
    (hfg : (j₀ ≫ q₀) ≫ (i₀ ≫ s₀) = (j₀ ≫ b₀) ≫ (p₀ ≫ s₀)) :
    c.pComp (j₀ ≫ q₀) (i₀ ≫ s₀) ≪≫ trianglePull c j₀ b₀ q₀ p₀ i₀ s₀ hb₀ =
      morphismPullbackCongr c hfg := by
  apply Iso.ext
  ext M
  exact trianglePull_cancel c j₀ b₀ q₀ p₀ i₀ s₀ hb₀ hfg M

private theorem iso_trans_app_eq
    {A B : Type*} [Category A] [Category B] {F G H : A ⥤ B}
    (e : F ≅ G) (d : G ≅ H) (t : F ≅ H) (h : e ≪≫ d = t) (M : A) :
    e.hom.app M ≫ d.hom.app M = t.hom.app M := by
  exact congrArg (fun z : F ≅ H ↦ z.hom.app M) h

private theorem tensor_transport_iso_map
    {A B : Type*} [Category A] [Category B] (R : A ≌ B) (T : A ⥤ A ⥤ A) (k : A)
    {a b c d e : A} (p : a ⟶ b)
    (r : b ≅ c) (s : c ⟶ d) (q : a ≅ e) (t : e ⟶ d)
    (x : R.functor.obj ((T.obj k).obj a) ⟶
      R.functor.obj ((T.obj k).obj b))
    (hx : x = R.functor.map ((T.obj k).map p))
    (h : p ≫ r.hom ≫ s = q.hom ≫ t)
    (E : R.inverse.obj (R.functor.obj ((T.obj k).obj b)) ≅
      (T.obj k).obj c) (hE : E = unitTensorRealization R T k r)
    (U : (T.obj k).obj a ≅ R.inverse.obj (R.functor.obj ((T.obj k).obj a)))
    (hU : U = R.unitIso.app ((T.obj k).obj a)) :
    R.inverse.map x ≫
        E.hom ≫ (T.obj k).map s =
      U.inv ≫
        (T.obj k).map q.hom ≫ (T.obj k).map t := by
  rw [hE, hU, hx]
  have h' := tensor_transport R (T.obj k) p r.hom s q.hom t h
  simpa only [unitTensorRealization, Iso.trans_hom, Iso.symm_hom, Iso.app_inv,
    Functor.mapIso_hom, Category.assoc] using h'

private theorem paste_two
    {A : Type*} [Category A] {a b c d e : A}
    (p : a ⟶ b) (r : b ⟶ c) (s : c ⟶ d) (q : a ⟶ e) (t : e ⟶ c) (u : e ⟶ d)
    (h : p ≫ r = q ≫ t) (h' : t ≫ s = u) : p ≫ r ≫ s = q ≫ u := by
  rw [← Category.assoc, h, Category.assoc, h']

private theorem tensorize_source
    {A B : Type*} [Category A] [Category B]
    (T : A ⥤ A ⥤ A) (R : A ⥤ B) (l : A)
    {a b c d e : A} (p : a ⟶ b) (q : b ≅ c) (r : c ≅ d) (s : d ⟶ e)
    (t : a ≅ e) (h : p ≫ q.hom ≫ r.hom ≫ s = t.hom) :
    R.map ((T.map p).app l) ≫
        (R.mapIso ((T.mapIso q).app l) ≪≫ R.mapIso ((T.mapIso r).app l)).hom ≫
        R.map ((Functor.uncurry.obj T).map (Prod.mkHom s (𝟙 l))) =
      (R.mapIso ((T.mapIso t).app l)).hom := by
  have h' := tensorize_four T R l p q.hom r.hom s t.hom h
  simpa only [Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, Category.assoc] using h'

private theorem uncurry_refl_iso
    {A : Type*} [Category A] (T : A ⥤ A ⥤ A) (k : A)
    {a b : A} (e : a ≅ b) :
    (Functor.uncurry.obj T).mapIso (Iso.prod (Iso.refl k) e) = (T.obj k).mapIso e := by
  apply Iso.ext
  change (T.map (𝟙 k)).app a ≫ (T.obj k).map e.hom = _
  simp only [CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp,
    Functor.mapIso_hom]

private theorem target_paste_iso
    {A B C : Type*} [Category A] [Category B] [Category C]
    (R : B ⥤ C) (F G : A ⥤ B) (alpha : F ⟶ G) (ha : IsIso alpha)
    {x₀ x₁ x₂ x₃ w₀ w₁ : A} {b₀ b₁ b₂ c₀ c₁ : C}
    (e : x₀ ⟶ x₁) (d : x₁ ≅ x₂) (t : x₂ ≅ x₃)
    (z₀ : x₀ ≅ w₀) (z₁ : w₀ ≅ w₁) (z₂ : w₁ ≅ x₃)
    (a : b₀ ⟶ b₁) (v : b₁ ⟶ b₂)
    (s₀ : b₁ ≅ c₀) (s₀' : c₀ ≅ R.obj (F.obj x₀))
    (s₁ : b₂ ≅ c₁) (s₁' : c₁ ≅ R.obj (F.obj x₁))
    (h₀ : b₀ ≅ R.obj (G.obj x₀))
    (hs : a ≫ s₀.hom ≫ s₀'.hom ≫ R.map (alpha.app x₀) = h₀.hom)
    (hn : v ≫ s₁.hom ≫ s₁'.hom = s₀.hom ≫ s₀'.hom ≫ R.map (F.map e))
    (hi : e ≫ d.hom ≫ t.hom = z₀.hom ≫ z₁.hom ≫ z₂.hom) :
    letI := ha
    (a ≫ v) ≫
        ((s₁ ≪≫ s₁' ≪≫ R.mapIso (F.mapIso d)) ≪≫
          R.mapIso ((asIso alpha).app x₂) ≪≫ R.mapIso (G.mapIso t)).hom =
      ((h₀ ≪≫ R.mapIso (G.mapIso (z₀ ≪≫ z₁))) ≪≫ R.mapIso (G.mapIso z₂)).hom := by
  let := ha
  have h := target_paste R F G alpha e d.hom t.hom
    (z₀.hom ≫ z₁.hom ≫ z₂.hom) a v
    (s₀ ≪≫ s₀').hom (s₁ ≪≫ s₁').hom h₀.hom
    (by simpa only [Iso.trans_hom, Category.assoc] using hs)
    (by simpa only [Iso.trans_hom, Category.assoc] using hn) hi
  simpa only [Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, asIso_hom,
    Functor.map_comp, Category.assoc] using h

section SupportComparisonAPI
attribute [local implicit_reducible] realization sixFunctorFiniteRealization
  sixFunctorFiniteSupport sfIntrinsicCompactSupport sfAmbientCompactSupportCandidate
  rightDerivedLowerShriek originCompactSupport comparisonUpperStarPlusEtaleOrigin
  Functor.asEquivalence Equivalence.congrLeft
attribute [local irreducible] sfIntrinsicCompactSupportComparison

private theorem inverseConjugation_component
    {A B C₀ D₀ : Type*} [Category A] [Category B] [Category C₀] [Category D₀]
    (R : A ≌ B) (R' : C₀ ≌ D₀) (F : B ⥤ D₀) (G : A ⥤ C₀)
    (e : R.functor ⋙ F ≅ G ⋙ R'.functor) (K : B) :
    (inverseConjugation R R' F G e).hom.app K =
      R'.inverse.map (F.map (R.counitIso.inv.app K) ≫
        e.hom.app (R.inverse.obj K)) ≫
      R'.unitIso.inv.app (G.obj (R.inverse.obj K)) := by
  simp only [inverseConjugation, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Iso.symm_hom,
    Functor.leftUnitor_inv_app, Functor.rightUnitor_hom_app, Functor.comp_obj,
    Category.id_comp]
  dsimp only [Functor.comp_obj, Functor.id_obj, Functor.id_map]
  simp only [Functor.map_comp, Category.comp_id, Category.assoc]

private theorem fixedSupportComparison_eq
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}
    (S : SixFunctorFiniteOperations D C E n hn)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    (cf : Compactification f.hom.left) (K : sixFunctorFiniteCategory D C E n hn X) :
    letI := Padic.finite_coefficientExtensionRing C.l E n hn
    (fixedSupportComparison S f cf).hom.app K = (fixedSupportRealization S f cf K).hom := by
  let := Padic.finite_coefficientExtensionRing C.l E n hn
  simp only [fixedSupportComparison, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, inverseConjugation_component,
    fixedSupportRealization, supportRealization, Functor.mapIso_hom, Iso.app_hom,
    Iso.app_inv, Iso.symm_hom, Functor.map_comp, Category.assoc]
  rfl

private theorem preimageIso_reverse
    {A B : Type*} [Category A] [Category B] {F : A ⥤ B}
    (hF : F.FullyFaithful) {a b : A} (e : F.obj a ≅ F.obj b) :
    (hF.preimageIso e).symm = hF.preimageIso e.symm := rfl

attribute [local irreducible] towerCandidateComparison compactSupportSiteComparison

private theorem candidateComparison_reverse
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f]
    (c d : Compactification f) :
    (towerCandidateComparison A c d).symm = towerCandidateComparison A d c := by
  have he : (Etale.rightDerivedLowerShriekOfCompactificationPlusιIso A c d).symm =
      Etale.rightDerivedLowerShriekOfCompactificationPlusιIso A d c := by
    simp only [Etale.rightDerivedLowerShriekOfCompactificationPlusιIso, Iso.trans_symm,
      Iso.symm_symm_eq, Functor.isoWhiskerRight_symm,
      Etale.rightDerivedLowerShriekOfCompactificationPlusIso_symm, Iso.trans_assoc]
  unfold towerCandidateComparison
  dsimp only
  rw [preimageIso_reverse]
  congr 1
  simp only [Iso.trans_symm, Iso.symm_symm_eq, Functor.isoWhiskerRight_symm,
    he, Iso.trans_assoc]

private theorem candidateCompositor_eq
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [QuasiCompact f] [QuasiCompact g]
    (cf : Compactification f) (cg : Compactification g)
    (cfg : Compactification (f ≫ g))
    (O : (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X).FullSubcategory) :
    letI := cf.hasCompactification
    letI := cg.hasCompactification
    letI := cfg.hasCompactification
    ProjectionTriangleAssembly.candidateCompositor A (f := f) (g := g) cf cg cfg O =
      (finiteSupportCandidateComposition A f g cf cg cfg).hom.app O := by
  let := cf.hasCompactification
  let := cg.hasCompactification
  let := cfg.hasCompactification
  have h := candidateComparison_reverse A
    (HasCompactification.compactification (f ≫ g)) cfg
  unfold ProjectionTriangleAssembly.candidateCompositor finiteSupportCandidateComposition
  exact congrArg
    (fun δ ↦ (finiteSupportCandidateCompositionCore
      (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X).ι
      (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) Y).ι
      (originCompactSupport A f)
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cf)
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cg)
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A) g)
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cfg)
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A) (f ≫ g))
      (towerCandidateComparison A cf (HasCompactification.compactification f))
      (towerCandidateComparison A cg (HasCompactification.compactification g))
      (originCompositionAmbient A f g) δ).hom.app O) h

end SupportComparisonAPI

variable {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
  {E : Type u} [Field E] [Algebra (Padic C.l) E]
  [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}
  (S : SixFunctorFiniteOperations D C E n hn)
  {X V W Y B Z : SixFunctorSpace D}
  (j : X ⟶ V) (b : V ⟶ W) (q : V ⟶ Y) (p : W ⟶ B) (i : Y ⟶ B) (s : B ⟶ Z)
  [IsOpenImmersion ((geometry D).map j)] [IsOpenImmersion ((geometry D).map b)]
  [IsOpenImmersion ((geometry D).map i)] [QuasiCompact ((geometry D).map b)]
    [QuasiCompact ((geometry D).map i)]
  [IsProper ((geometry D).map q)] [IsProper ((geometry D).map p)] [IsProper ((geometry D).map s)]
  (hb : b ≫ p = q ≫ i)

section BinaryProof
attribute [local implicit_reducible] realization sixFunctorFiniteRealization
  sixFunctorFiniteSupport sfIntrinsicCompactSupport sfAmbientCompactSupportCandidate
  originInclusion ordinary sixFunctorFactorCompactification compact
  binaryFirst binarySecond binaryTotal finiteTorConstructible
attribute [local irreducible] sfIntrinsicCompactSupportComparison
  alpha towerCandidateComparison originCompositionAmbient
  ProjectionTriangleAssembly.candidateCompositor

private theorem partialTensor_map_first
    {M N : sixFunctorFiniteCategory D C E n hn X} (a : M ⟶ N)
    (L : finiteTorConstructibleCategory C.l E n hn X.obj.left) :
    letI := Padic.finite_coefficientExtensionRing C.l E n hn
    let R := realization (C := C) (E := E) (n := n) (hn := hn) X
    let T := fixedTensor (C := C) (E := E) (n := n) X
    let I := (intrinsicFiniteTorsionConstructible C.l E n hn X.obj.left).ι
    I.map (((partialTensor S X).map a).app L) =
      R.functor.map ((T.map (R.inverse.map a.hom)).app (R.inverse.obj L.obj)) := by
  let := Padic.finite_coefficientExtensionRing C.l E n hn
  let R := realization (C := C) (E := E) (n := n) (hn := hn) X
  let T := fixedTensor (C := C) (E := E) (n := n) X
  change R.functor.map ((T.map (R.inverse.map a.hom)).app (R.inverse.obj L.obj)) ≫
    R.functor.map ((T.obj (R.inverse.obj N.obj)).map (R.inverse.map (𝟙 L.obj))) = _
  simp only [CategoryTheory.Functor.map_id, Category.comp_id]
  rfl

private theorem partialTensor_map_second
    (K : sixFunctorFiniteCategory D C E n hn X)
    {L M : finiteTorConstructibleCategory C.l E n hn X.obj.left} (a : L ⟶ M) :
    letI := Padic.finite_coefficientExtensionRing C.l E n hn
    let R := realization (C := C) (E := E) (n := n) (hn := hn) X
    let T := fixedTensor (C := C) (E := E) (n := n) X
    let I := (intrinsicFiniteTorsionConstructible C.l E n hn X.obj.left).ι
    I.map (((partialTensor S X).obj K).map a) =
      R.functor.map ((T.obj (R.inverse.obj K.obj)).map (R.inverse.map a.hom)) := by
  let := Padic.finite_coefficientExtensionRing C.l E n hn
  let R := realization (C := C) (E := E) (n := n) (hn := hn) X
  let T := fixedTensor (C := C) (E := E) (n := n) X
  change R.functor.map ((T.map (R.inverse.map (𝟙 K.obj))).app (R.inverse.obj L.obj)) ≫
    R.functor.map ((T.obj (R.inverse.obj K.obj)).map (R.inverse.map a.hom)) = _
  simp only [CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp]
  rfl

private theorem support_binary_fixed
    (sq : IsPullback b.hom.left q.hom.left p.hom.left i.hom.left)
    (K : sixFunctorFiniteCategory D C E n hn X) :
    letI := Padic.finite_coefficientExtensionRing C.l E n hn
    let A := ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)
    let RZ := realization (C := C) (E := E) (n := n) (hn := hn) Z
    let RX := realization (C := C) (E := E) (n := n) (hn := hn) X
    RZ.inverse.map ((S.finite.composition (j ≫ q) (i ≫ s)
      (binaryFirst j q) (binarySecond i s) (binaryTotal j b q p i s hb)).inv.app K).hom ≫
        (fixedSupportRealization S ((j ≫ q) ≫ (i ≫ s))
          (binaryTotal j b q p i s hb) K).hom =
      (fixedSupportRealization S (i ≫ s) (binarySecond i s)
        ((S.finite.support (j ≫ q) (binaryFirst j q)).obj K)).hom ≫
      (compact (ordinary D A) i s).map
        (fixedSupportRealization S (j ≫ q) (binaryFirst j q) K).hom ≫
      (alpha (ordinary D A) j b q p i s hb).app (RX.inverse.obj K.obj) := by
  let := Padic.finite_coefficientExtensionRing C.l E n hn
  let A := ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)
  let : QuasiCompact (j ≫ q).hom.left := by
    have := spaceNoetherian X
    have := spaceNoetherian Y
    infer_instance
  let : QuasiCompact (i ≫ s).hom.left := by
    have := spaceNoetherian Y
    have := spaceNoetherian Z
    infer_instance
  let cf := binaryFirst j q
  let cg := binarySecond i s
  let cfg := binaryTotal j b q p i s hb
  let := cf.hasCompactification
  let := cg.hasCompactification
  let := cfg.hasCompactification
  let : HasCompactification ((j ≫ q).hom.left ≫ (i ≫ s).hom.left) :=
    cfg.hasCompactification
  have h := fixedSupportComparison_composition_app S (j ≫ q) (i ≫ s) cf cg cfg K
  dsimp only at h
  rw [fixedSupportComparison_eq, fixedSupportComparison_eq,
    fixedSupportComparison_eq] at h
  have hc := cartesianCompactSupportCompositor D A j b q p i s hb sq
    ((originInclusion (C := C) (E := E) (n := n) (hn := hn) X).obj K)
  change (alpha (ordinary D A) j b q p i s hb).app
    ((realization (C := C) (E := E) (n := n) (hn := hn) X).inverse.obj K.obj) =
      ProjectionTriangleAssembly.candidateCompositor A
        (f := (j ≫ q).hom.left) (g := (i ≫ s).hom.left) cf cg cfg
        ((originInclusion (C := C) (E := E) (n := n) (hn := hn) X).obj K) at hc
  rw [candidateCompositor_eq] at hc
  dsimp only
  rw [hc]
  exact h

private theorem support_binary_forward
    (sq : IsPullback b.hom.left q.hom.left p.hom.left i.hom.left)
    (M : sixFunctorFiniteCategory D C E n hn X) :
    letI := Padic.finite_coefficientExtensionRing C.l E n hn
    let A := ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)
    let RX := realization (C := C) (E := E) (n := n) (hn := hn) X
    let RZ := realization (C := C) (E := E) (n := n) (hn := hn) Z
    let I := (intrinsicFiniteTorsionConstructible C.l E n hn Z.obj.left).ι
    let f := j ≫ q
    let g := i ≫ s
    let cf := binaryFirst j q
    let cg := binarySecond i s
    let cfg := binaryTotal j b q p i s hb
    I.map ((S.finite.composition f g cf cg cfg).hom.app M) ≫
      (supportRealization S g cg ((S.finite.support f cf).obj M)).hom ≫
      RZ.functor.map ((compact (ordinary D A) i s).map
        (fixedSupportRealization S f cf M).hom) ≫
      RZ.functor.map ((alpha (ordinary D A) j b q p i s hb).app
        (RX.inverse.obj M.obj)) = (supportRealization S (f ≫ g) cfg M).hom := by
  let := Padic.finite_coefficientExtensionRing C.l E n hn
  let A := ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)
  let RX := realization (C := C) (E := E) (n := n) (hn := hn) X
  let RZ := realization (C := C) (E := E) (n := n) (hn := hn) Z
  let f := j ≫ q
  let g := i ≫ s
  let cf := binaryFirst j q
  let cg := binarySecond i s
  let cfg := binaryTotal j b q p i s hb
  let I := (intrinsicFiniteTorsionConstructible C.l E n hn Z.obj.left).ι
  let e := RZ.inverse.mapIso (I.mapIso ((S.finite.composition f g cf cg cfg).app M))
  have h := forward_of_inverse e _ _ (support_binary_fixed S j b q p i s hb sq M)
  have h' := realize_triangle RZ (supportRealization S (f ≫ g) cfg M)
    (supportRealization S g cg ((S.finite.support f cf).obj M))
    (I.map ((S.finite.composition f g cf cg cfg).hom.app M))
    ((compact (ordinary D A) i s).map (fixedSupportRealization S f cf M).hom ≫
      (alpha (ordinary D A) j b q p i s hb).app (RX.inverse.obj M.obj))
    (by simpa only [e, Functor.mapIso_hom, Iso.app_hom, fixedSupportRealization,
      Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Iso.app_inv,
      Category.assoc (obj := (ordinary D A).D Z)] using h)
  simpa only [Functor.map_comp, Category.assoc (obj := proEtaleDerivedCategory Z.obj.left
        (Padic.coefficientExtensionRing C.l E n))] using h'

private theorem iteration_support_naturality
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}
    (S : SixFunctorFiniteOperations D C E n hn)
    {X Y Z : SixFunctorSpace D} (f : X ⟶ Y) (g : Y ⟶ Z)
    (cf : Compactification f.hom.left) (cg : Compactification g.hom.left)
    {M N : sixFunctorFiniteCategory D C E n hn X} (a : M ⟶ N) :
    letI := Padic.finite_coefficientExtensionRing C.l E n hn
    let RX := realization (C := C) (E := E) (n := n) (hn := hn) X
    let RZ := realization (C := C) (E := E) (n := n) (hn := hn) Z
    let IX := (intrinsicFiniteTorsionConstructible C.l E n hn X.obj.left).ι
    let IZ := (intrinsicFiniteTorsionConstructible C.l E n hn Z.obj.left).ι
    let F := sfFixedCompactSupport (Padic.coefficientExtensionRing C.l E n) cf
    let G := sfFixedCompactSupport (Padic.coefficientExtensionRing C.l E n) cg
    IZ.map ((S.finite.support g cg).map ((S.finite.support f cf).map a)) ≫
      (supportRealization S g cg ((S.finite.support f cf).obj N)).hom ≫
      RZ.functor.map (G.map (fixedSupportRealization S f cf N).hom) =
    (supportRealization S g cg ((S.finite.support f cf).obj M)).hom ≫
      RZ.functor.map (G.map (fixedSupportRealization S f cf M).hom) ≫
      RZ.functor.map (G.map (F.map (RX.inverse.map (IX.map a)))) := by
  let := Padic.finite_coefficientExtensionRing C.l E n hn
  let A := ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)
  let RX := realization (C := C) (E := E) (n := n) (hn := hn) X
  let RZ := realization (C := C) (E := E) (n := n) (hn := hn) Z
  let IZ := (intrinsicFiniteTorsionConstructible C.l E n hn Z.obj.left).ι
  let F := sfFixedCompactSupport (Padic.coefficientExtensionRing C.l E n) cf
  let G := sfFixedCompactSupport (Padic.coefficientExtensionRing C.l E n) cg
  have hg := fixed_support_naturality S g cg ((S.finite.support f cf).map a)
  have hf := congrArg G.map (fixed_support_naturality S f cf a)
  simp only [Functor.map_comp] at hf
  have h' := realize_square_tail RZ
    (supportRealization S g cg ((S.finite.support f cf).obj M))
    (supportRealization S g cg ((S.finite.support f cf).obj N))
    (IZ.map ((S.finite.support g cg).map ((S.finite.support f cf).map a)))
    (G.map (fixedSupportRealization S f cf N).hom)
    (G.map (fixedSupportRealization S f cf M).hom ≫
      G.map (F.map (RX.inverse.map a.hom))) (by
      have hgg := congrArg
        (fun z ↦ z ≫ G.map (fixedSupportRealization S f cf N).hom) hg
      simp only [Category.assoc (obj := (ordinary D A).D Z)] at hgg
      rw [hf] at hgg
      simp -implicitDefEqProofs only [fixedSupportRealization, Iso.trans_hom,
        Functor.mapIso_hom, Iso.symm_hom, Iso.app_inv,
        Category.assoc (obj := (ordinary D A).D Z)] at hgg ⊢
      convert hgg using 1 <;> rfl)
  simp -implicitDefEqProofs only [Functor.map_comp] at h'
  convert h' using 1
  rfl

omit [IsOpenImmersion ((geometry D).map j)] [IsOpenImmersion ((geometry D).map b)]
  [IsOpenImmersion ((geometry D).map i)] [QuasiCompact ((geometry D).map b)]
  [QuasiCompact ((geometry D).map i)] [IsProper ((geometry D).map q)]
  [IsProper ((geometry D).map p)] [IsProper ((geometry D).map s)] in
private theorem pull_binary_normalization
    (L : finiteTorConstructibleCategory C.l E n hn Z.obj.left) :
    letI := Padic.finite_coefficientExtensionRing C.l E n hn
    let A := ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)
    let RX := realization (C := C) (E := E) (n := n) (hn := hn) X
    let RZ := realization (C := C) (E := E) (n := n) (hn := hn) Z
    let IX := (intrinsicFiniteTorsionConstructible C.l E n hn X.obj.left).ι
    let f := j ≫ q
    let g := i ≫ s
    let N : sixFunctorFiniteCategory D C E n hn Z := ⟨L.obj, L.property.1⟩
    RX.inverse.map (IX.map ((S.finite.pullComposition f g).hom.app N)) ≫
      (fixedPullRealization S f ((S.finite.pull g).obj N) ≪≫
        (fixedDerivedPull (C := C) (E := E) (n := n) f).mapIso
          (fixedPullRealization S g N)).hom =
    (fixedPullRealization S (f ≫ g) N).hom ≫
      ((ordinary D A).pComp f g).hom.app (RZ.inverse.obj L.obj) := by
  exact fixedPullRealization_composition S (j ≫ q) (i ≫ s) ⟨L.obj, L.property.1⟩

omit [IsOpenImmersion ((geometry D).map j)] [IsOpenImmersion ((geometry D).map b)]
  [IsOpenImmersion ((geometry D).map i)] [QuasiCompact ((geometry D).map b)]
  [QuasiCompact ((geometry D).map i)] [IsProper ((geometry D).map q)]
  [IsProper ((geometry D).map p)] [IsProper ((geometry D).map s)] in
private theorem pull_binary_cancelIso
    (A : Type (u + 1)) [CommRing A] [Finite A] :
    (ordinary D A).pComp (j ≫ q) (i ≫ s) ≪≫
      trianglePull (ordinary D A) j b q p i s hb =
    binaryPullCast j b q p i s hb A := by
  exact trianglePull_cancelIso (ordinary D A) j b q p i s hb
    (by
      simp only [Category.assoc]
      rw [← Category.assoc q i s, ← hb]
      simp only [Category.assoc])

omit [IsOpenImmersion ((geometry D).map j)] [IsOpenImmersion ((geometry D).map b)]
  [IsOpenImmersion ((geometry D).map i)] [QuasiCompact ((geometry D).map b)]
  [QuasiCompact ((geometry D).map i)] [IsProper ((geometry D).map q)]
  [IsProper ((geometry D).map p)] [IsProper ((geometry D).map s)] in
private theorem pull_binary_cancel
    (A : Type (u + 1)) [CommRing A] [Finite A] (M : (ordinary D A).D Z) :
    ((ordinary D A).pComp (j ≫ q) (i ≫ s)).hom.app M ≫
      (trianglePull (ordinary D A) j b q p i s hb).hom.app M =
    (binaryPullCast j b q p i s hb A).hom.app M := by
  exact iso_trans_app_eq _ _ _ (pull_binary_cancelIso j b q p i s hb A) M

omit [IsOpenImmersion ((geometry D).map j)] [IsOpenImmersion ((geometry D).map b)]
  [IsOpenImmersion ((geometry D).map i)] [QuasiCompact ((geometry D).map b)]
  [QuasiCompact ((geometry D).map i)] [IsProper ((geometry D).map q)]
  [IsProper ((geometry D).map p)] [IsProper ((geometry D).map s)] in
private theorem pull_binary_input
    (L : finiteTorConstructibleCategory C.l E n hn Z.obj.left) :
    letI := Padic.finite_coefficientExtensionRing C.l E n hn
    let A := ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)
    let RX := realization (C := C) (E := E) (n := n) (hn := hn) X
    let RZ := realization (C := C) (E := E) (n := n) (hn := hn) Z
    let IX := (intrinsicFiniteTorsionConstructible C.l E n hn X.obj.left).ι
    let f := j ≫ q
    let g := i ≫ s
    let N : sixFunctorFiniteCategory D C E n hn Z := ⟨L.obj, L.property.1⟩
    RX.inverse.map (IX.map ((S.finite.pullComposition f g).hom.app N)) ≫
      (fixedPullRealization S f ((S.finite.pull g).obj N) ≪≫
        (fixedDerivedPull (C := C) (E := E) (n := n) f).mapIso
          (fixedPullRealization S g N)).hom ≫
      (trianglePull (ordinary D A) j b q p i s hb).hom.app (RZ.inverse.obj L.obj) =
    (fixedPullRealization S (f ≫ g) N).hom ≫
      (binaryPullCast j b q p i s hb A).hom.app (RZ.inverse.obj L.obj) := by
  let := Padic.finite_coefficientExtensionRing C.l E n hn
  let A := ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)
  let RX := realization (C := C) (E := E) (n := n) (hn := hn) X
  let RZ := realization (C := C) (E := E) (n := n) (hn := hn) Z
  let IX := (intrinsicFiniteTorsionConstructible C.l E n hn X.obj.left).ι
  let f := j ≫ q
  let g := i ≫ s
  let N : sixFunctorFiniteCategory D C E n hn Z := ⟨L.obj, L.property.1⟩
  let pullArrow := RX.inverse.map (IX.map ((S.finite.pullComposition f g).hom.app N))
  let r := fixedPullRealization S f ((S.finite.pull g).obj N) ≪≫
    (fixedDerivedPull (C := C) (E := E) (n := n) f).mapIso (fixedPullRealization S g N)
  let q₀ := fixedPullRealization S (f ≫ g) N
  let a := (trianglePull (ordinary D A) j b q p i s hb).hom.app (RZ.inverse.obj L.obj)
  let c := (binaryPullCast j b q p i s hb A).hom.app (RZ.inverse.obj L.obj)
  have hp : pullArrow ≫ r.hom = q₀.hom ≫
      ((ordinary D A).pComp f g).hom.app (RZ.inverse.obj L.obj) :=
    pull_binary_normalization S j q i s L
  have hcancel : ((ordinary D A).pComp f g).hom.app (RZ.inverse.obj L.obj) ≫
      a = c := by
    exact pull_binary_cancel j b q p i s hb A (RZ.inverse.obj L.obj)
  exact paste_two pullArrow r.hom a q₀.hom
    (((ordinary D A).pComp f g).hom.app (RZ.inverse.obj L.obj)) c hp hcancel

omit [IsOpenImmersion ((geometry D).map j)] [IsOpenImmersion ((geometry D).map b)]
  [IsOpenImmersion ((geometry D).map i)] [QuasiCompact ((geometry D).map b)]
  [QuasiCompact ((geometry D).map i)] [IsProper ((geometry D).map q)]
  [IsProper ((geometry D).map p)] [IsProper ((geometry D).map s)] in
private theorem iteration_tensor_core
    (K : sixFunctorFiniteCategory D C E n hn X)
    (L : finiteTorConstructibleCategory C.l E n hn Z.obj.left) :
    letI := Padic.finite_coefficientExtensionRing C.l E n hn
    let RX := realization (C := C) (E := E) (n := n) (hn := hn) X
    let TX := fixedTensor (C := C) (E := E) (n := n) X
    let N : sixFunctorFiniteCategory D C E n hn Z := ⟨L.obj, L.property.1⟩
    iterationTensorComparison S (j ≫ q) (i ≫ s) K L =
      unitTensorRealization RX TX (RX.inverse.obj K.obj)
        (fixedPullRealization S (j ≫ q) ((S.finite.pull (i ≫ s)).obj N) ≪≫
          (fixedDerivedPull (C := C) (E := E) (n := n) (j ≫ q)).mapIso
            (fixedPullRealization S (i ≫ s) N)) := by
  dsimp only [iterationTensorComparison]
  congr 1

omit [IsOpenImmersion ((geometry D).map j)] [IsOpenImmersion ((geometry D).map b)]
  [IsOpenImmersion ((geometry D).map i)] [QuasiCompact ((geometry D).map b)]
  [QuasiCompact ((geometry D).map i)] [IsProper ((geometry D).map q)]
  [IsProper ((geometry D).map p)] [IsProper ((geometry D).map s)] in
set_option cleanup.letToHave false in
private theorem tensor_binary_abstract
    (RX : DerivedCategory (Sheaf (ProEt.topology X.obj.left)
      (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)))) ≌
      proEtaleDerivedCategory X.obj.left (Padic.coefficientExtensionRing C.l E n))
    (TX : DerivedCategory (Sheaf (ProEt.topology X.obj.left)
      (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)))) ⥤
      DerivedCategory (Sheaf (ProEt.topology X.obj.left)
      (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)))) ⥤
      DerivedCategory (Sheaf (ProEt.topology X.obj.left)
      (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)))))
    (K : sixFunctorFiniteCategory D C E n hn X)
    (L : finiteTorConstructibleCategory C.l E n hn Z.obj.left) :
    letI := Padic.finite_coefficientExtensionRing C.l E n hn
    let A := ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)
    let RZ := realization (C := C) (E := E) (n := n) (hn := hn) Z
    let IX := (intrinsicFiniteTorsionConstructible C.l E n hn X.obj.left).ι
    let f := j ≫ q
    let g := i ≫ s
    let k := RX.inverse.obj K.obj
    let N : sixFunctorFiniteCategory D C E n hn Z := ⟨L.obj, L.property.1⟩
    ∀ (r : RX.inverse.obj ((S.finite.pull f).obj ((S.finite.pull g).obj N)).obj ≅
        (fixedDerivedPull (C := C) (E := E) (n := n) f).obj
          ((fixedDerivedPull (C := C) (E := E) (n := n) g).obj
            (RZ.inverse.obj L.obj)))
      (qa : RX.inverse.obj ((S.finite.pull (f ≫ g)).obj N).obj ≅
        (fixedDerivedPull (C := C) (E := E) (n := n) (f ≫ g)).obj
          (RZ.inverse.obj L.obj)),
    ∀ (s₀ : ((ordinary D A).P g ⋙ (ordinary D A).P f).obj
        (RZ.inverse.obj L.obj) ⟶
        ((ordinary D A).P ((j ≫ b) ≫ (p ≫ s))).obj (RZ.inverse.obj L.obj))
      (t₀ : ((ordinary D A).P (f ≫ g)).obj (RZ.inverse.obj L.obj) ⟶
        ((ordinary D A).P ((j ≫ b) ≫ (p ≫ s))).obj (RZ.inverse.obj L.obj)),
    ∀ (x : RX.functor.obj ((TX.obj k).obj
        (RX.inverse.obj ((torPull S (f ≫ g)).obj L).obj)) ⟶
      RX.functor.obj ((TX.obj k).obj
        (RX.inverse.obj ((torPull S f).obj ((torPull S g).obj L)).obj)))
      (e : RX.inverse.obj (RX.functor.obj ((TX.obj k).obj
          (RX.inverse.obj ((S.finite.pull f).obj
            ⟨((torPull S g).obj L).obj, ((torPull S g).obj L).property.1⟩).obj))) ≅
        (TX.obj k).obj ((fixedDerivedPull (C := C) (E := E) (n := n) f).obj
          ((fixedDerivedPull (C := C) (E := E) (n := n) g).obj
            (RZ.inverse.obj L.obj)))),
      RX.inverse.map (IX.map ((S.finite.pullComposition f g).hom.app N)) ≫
          r.hom ≫ s₀ =
        qa.hom ≫ t₀ →
      e = unitTensorRealization RX TX k r →
      x = RX.functor.map ((TX.obj k).map
        (RX.inverse.map (IX.map ((S.finite.pullComposition f g).hom.app N)))) →
      RX.inverse.map x ≫ e.hom ≫
        (TX.obj k).map (s₀) =
      (RX.unitIso.app
        ((TX.obj k).obj (RX.inverse.obj ((torPull S (f ≫ g)).obj L).obj))).inv ≫
        (TX.obj k).map qa.hom ≫
        (TX.obj k).map (t₀) := by
  intros
  rename_i A RZ IX f g k N r qa s₀ t₀ x e ht he hx
  exact tensor_transport_iso_map RX TX k
    (a := RX.inverse.obj ((torPull S (f ≫ g)).obj L).obj)
    (RX.inverse.map (IX.map ((S.finite.pullComposition f g).hom.app N)))
    r s₀ qa t₀ x hx ht e he
    (RX.unitIso.app ((TX.obj k).obj
      (RX.inverse.obj ((torPull S (f ≫ g)).obj L).obj))) rfl

omit [IsOpenImmersion ((geometry D).map j)] [IsOpenImmersion ((geometry D).map b)]
  [IsOpenImmersion ((geometry D).map i)] [QuasiCompact ((geometry D).map b)]
  [QuasiCompact ((geometry D).map i)] [IsProper ((geometry D).map q)]
  [IsProper ((geometry D).map p)] [IsProper ((geometry D).map s)] in
private theorem partialTensor_pull_composition
    (K : sixFunctorFiniteCategory D C E n hn X)
    (L : finiteTorConstructibleCategory C.l E n hn Z.obj.left) :
    letI := Padic.finite_coefficientExtensionRing C.l E n hn
    let RX := realization (C := C) (E := E) (n := n) (hn := hn) X
    let TX := fixedTensor (C := C) (E := E) (n := n) X
    let IX := (intrinsicFiniteTorsionConstructible C.l E n hn X.obj.left).ι
    let f := j ≫ q
    let g := i ≫ s
    let N : sixFunctorFiniteCategory D C E n hn Z := ⟨L.obj, L.property.1⟩
    IX.map (((partialTensor S X).obj K).map (torPullComposition S f g L).hom) =
      RX.functor.map ((TX.obj (RX.inverse.obj K.obj)).map
        (RX.inverse.map (IX.map ((S.finite.pullComposition f g).hom.app N)))) := by
  let := Padic.finite_coefficientExtensionRing C.l E n hn
  intros
  rename_i RX TX IX f g N
  have ha : (torPullComposition S f g L).hom.hom =
      IX.map ((S.finite.pullComposition f g).hom.app N) := by rfl
  exact (partialTensor_map_second S K (torPullComposition S f g L).hom).trans
    (congrArg (fun z ↦ RX.functor.map ((TX.obj (RX.inverse.obj K.obj)).map
      (RX.inverse.map z))) ha)

omit [IsOpenImmersion ((geometry D).map j)] [IsOpenImmersion ((geometry D).map b)]
  [IsOpenImmersion ((geometry D).map i)] [QuasiCompact ((geometry D).map b)]
  [QuasiCompact ((geometry D).map i)] [IsProper ((geometry D).map q)]
  [IsProper ((geometry D).map p)] [IsProper ((geometry D).map s)] in
set_option cleanup.letToHave false in
private theorem tensor_binary_calculation
    (K : sixFunctorFiniteCategory D C E n hn X)
    (L : finiteTorConstructibleCategory C.l E n hn Z.obj.left) :
    letI := Padic.finite_coefficientExtensionRing C.l E n hn
    let RX := realization (C := C) (E := E) (n := n) (hn := hn) X
    let TX := fixedTensor (C := C) (E := E) (n := n) X
    let A := ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)
    let RZ := realization (C := C) (E := E) (n := n) (hn := hn) Z
    let IX := (intrinsicFiniteTorsionConstructible C.l E n hn X.obj.left).ι
    let f := j ≫ q
    let g := i ≫ s
    let k := RX.inverse.obj K.obj
    let N : sixFunctorFiniteCategory D C E n hn Z := ⟨L.obj, L.property.1⟩
    let r := fixedPullRealization S f ((S.finite.pull g).obj N) ≪≫
      (fixedDerivedPull (C := C) (E := E) (n := n) f).mapIso (fixedPullRealization S g N)
    let qa := fixedPullRealization S (f ≫ g) N
    let s₀ := (trianglePull (ordinary D A) j b q p i s hb).hom.app
      (RZ.inverse.obj L.obj)
    let t₀ := (binaryPullCast j b q p i s hb A).hom.app (RZ.inverse.obj L.obj)
    let x := IX.map (((partialTensor S X).obj K).map
      (torPullComposition S f g L).hom)
    let e := iterationTensorComparison S f g K L;
      RX.inverse.map (IX.map ((S.finite.pullComposition f g).hom.app N)) ≫
          r.hom ≫ s₀ =
        qa.hom ≫ t₀ →
      e = unitTensorRealization RX TX k r →
      x = RX.functor.map ((TX.obj k).map
        (RX.inverse.map (IX.map ((S.finite.pullComposition f g).hom.app N)))) →
      RX.inverse.map x ≫ e.hom ≫
        (TX.obj k).map (s₀) =
      (RX.unitIso.app
        ((TX.obj k).obj (RX.inverse.obj ((torPull S (f ≫ g)).obj L).obj))).inv ≫
        (TX.obj k).map qa.hom ≫
        (TX.obj k).map (t₀) := by
  let := Padic.finite_coefficientExtensionRing C.l E n hn
  intros
  rename_i RX TX A RZ IX f g k N r qa s₀ t₀ x e ht he hx
  exact tensor_binary_abstract S j b q p i s RX TX K L r qa s₀ t₀ x e ht he hx

omit [IsOpenImmersion ((geometry D).map j)] [IsOpenImmersion ((geometry D).map b)]
  [IsOpenImmersion ((geometry D).map i)] [QuasiCompact ((geometry D).map b)]
  [QuasiCompact ((geometry D).map i)] [IsProper ((geometry D).map q)]
  [IsProper ((geometry D).map p)] [IsProper ((geometry D).map s)] in
private theorem tensor_binary_input
    (K : sixFunctorFiniteCategory D C E n hn X)
    (L : finiteTorConstructibleCategory C.l E n hn Z.obj.left) :
    letI := Padic.finite_coefficientExtensionRing C.l E n hn
    let A := ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)
    let RX := realization (C := C) (E := E) (n := n) (hn := hn) X
    let RZ := realization (C := C) (E := E) (n := n) (hn := hn) Z
    let IX := (intrinsicFiniteTorsionConstructible C.l E n hn X.obj.left).ι
    let TX := fixedTensor (C := C) (E := E) (n := n) X
    let f := j ≫ q
    let g := i ≫ s
    let k := RX.inverse.obj K.obj
    RX.inverse.map (IX.map
        (((partialTensor S X).obj K).map (torPullComposition S f g L).hom)) ≫
      (iterationTensorComparison S f g K L).hom ≫
      (TX.obj k).map ((trianglePull (ordinary D A) j b q p i s hb).hom.app
        (RZ.inverse.obj L.obj)) =
    (RX.unitIso.app
      ((TX.obj k).obj (RX.inverse.obj ((torPull S (f ≫ g)).obj L).obj))).inv ≫
      (TX.obj k).map (fixedPullRealization S (f ≫ g) ⟨L.obj, L.property.1⟩).hom ≫
      (TX.obj k).map ((binaryPullCast j b q p i s hb A).hom.app
        (RZ.inverse.obj L.obj)) := by
  exact tensor_binary_calculation S j b q p i s hb K L
    (pull_binary_input S j b q p i s hb L)
    (iteration_tensor_core S j q i s K L)
    (partialTensor_pull_composition S j q i s K L)

/-- The source endpoint of binary composition normalization.
Source: coefficient transport in fix-prop-projection-formula.proof.md.
(blueprint: lem-sf-finite-projection-composition-source).

Proof: the inverse-coordinate support normalization identifies the prescribed
support compositor with the raw Cartesian triangle arrow. Cancel its inverse to
obtain the forward normalization, then apply the fixed tensor in the support
slot with the fixed presentation of L. The explicit source comparisons and
functoriality of the curried tensor give exactly this endpoint equation. -/
theorem binary_composition_source
    (sq : IsPullback b.hom.left q.hom.left p.hom.left i.hom.left)
    (K : sixFunctorFiniteCategory D C E n hn X)
    (L : finiteTorConstructibleCategory C.l E n hn Z.obj.left) :
    letI := Padic.finite_coefficientExtensionRing C.l E n hn
    let A := ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)
    let RX := realization (C := C) (E := E) (n := n) (hn := hn) X
    let RZ := realization (C := C) (E := E) (n := n) (hn := hn) Z
    let I := (intrinsicFiniteTorsionConstructible C.l E n hn Z.obj.left).ι
    let f := j ≫ q
    let g := i ≫ s
    let cf := binaryFirst j q
    let cg := binarySecond i s
    let cfg := binaryTotal j b q p i s hb
    I.map (((partialTensor S Z).map
      ((S.finite.composition f g cf cg cfg).hom.app K)).app L) ≫
      (iterationSourceComparison S f g cf cg K L).hom ≫
        RZ.functor.map
          (((fixedScalarTensorData (C := C) (E := E) (n := n) (hn := hn)).tensor Z).map
            (Prod.mkHom ((alpha (ordinary D A) j b q p i s hb).app
              (RX.inverse.obj K.obj)) (𝟙 (RZ.inverse.obj L.obj)))) =
      (sourceComparison S (f ≫ g) cfg K L).hom := by
  let := Padic.finite_coefficientExtensionRing C.l E n hn
  let RX := realization (C := C) (E := E) (n := n) (hn := hn) X
  let RZ := realization (C := C) (E := E) (n := n) (hn := hn) Z
  let TZ := fixedTensor (C := C) (E := E) (n := n) Z
  let f := j ≫ q
  let g := i ≫ s
  let cf := binaryFirst j q
  let cg := binarySecond i s
  let cfg := binaryTotal j b q p i s hb
  let I := (intrinsicFiniteTorsionConstructible C.l E n hn Z.obj.left).ι
  let e := RZ.inverse.mapIso (I.mapIso ((S.finite.composition f g cf cg cfg).app K))
  have h := support_binary_fixed S j b q p i s hb sq K
  have hf := forward_of_inverse e _ _ h
  dsimp only [e, Functor.mapIso_hom, Iso.app_hom] at hf
  dsimp only
  rw [partialTensor_map_first S ((S.finite.composition f g cf cg cfg).hom.app K) L]
  exact tensorize_source TZ RZ.functor (RZ.inverse.obj L.obj)
    (RZ.inverse.map (I.map ((S.finite.composition f g cf cg cfg).hom.app K)))
    (fixedSupportRealization S g cg ((S.finite.support f cf).obj K))
    ((sfFixedCompactSupport (Padic.coefficientExtensionRing C.l E n) cg).mapIso
      (fixedSupportRealization S f cf K))
    ((alpha (ordinary D (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)))
      j b q p i s hb).app (RX.inverse.obj K.obj))
    (fixedSupportRealization S (f ≫ g) cfg K) hf

end BinaryProof

end WeilConjectures.CompactSupportFiniteProjection
