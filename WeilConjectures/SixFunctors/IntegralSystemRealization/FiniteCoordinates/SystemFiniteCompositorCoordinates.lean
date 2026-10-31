/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralSystemRealization.FiniteCoordinates.SystemFiniteEvaluationCoordinates
public import WeilConjectures.AlgebraicGeometry.AmbientProperOpen.RefinementProjection.RefinementProjectionWords
import WeilConjectures.SmoothPurity.IntegralSystemRealization.SystemPullbackCompositorEvaluation
import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicDirectCompositorCoordinates

/-! # Finite evaluation of a direct-image compositor

Source: Stacks 03DI, 07A7, 0F7B and the compactification-independence paragraph
of prop-sf-pf-coherence.proof.md.
(blueprint: lem-sf-system-finite-compositor-coordinates).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
open scoped CategoryTheory.TwoSquare
open AlgebraicGeometry.ProEtale.AmbientProperOpen
open AlgebraicGeometry.ProEtale.AmbientProperOpen.RefinementProjection
namespace WeilConjectures.IntegralSystemRealization.FiniteCoordinates

attribute [local implicit_reducible] integralCoefficientSheaf integralCoefficientCommRingSheaf
  scalarReductionTargetDerived

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

attribute [local irreducible] HasDerivedCategory.standard Functor.mapDerivedCategory
  Functor.rightDerivedFunctor CategoryTheory.constantSheaf
  AlgebraicGeometry.Scheme.residueField coefficientSequenceCommRingSheaf
  coefficientSequenceCommRingPresheaf sfIntrinsicExtensionByZero
  sfIntrinsicDerivedEquivalence sfIntrinsicDerivedDirectImageComparison
  sfIntrinsicDerivedPullbackComp

private theorem evaluation_is_mate (o : Operations l E) (m : ℕ)
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (mateEquiv (o.direct f).adj (finiteAdj l E f m)
      (TwoSquare.mk _ _ _ _ (pullbackTensorDerivedEvaluation l E f m).inv)).natTrans =
        ((o.evaluation f).evaluation m).hom := by
  ext M
  apply ((finiteAdj l E f m).homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit]
  rw [mateEquiv_counit]
  apply (cancel_epi ((pullbackTensorDerivedEvaluation l E f m).hom.app
    ((Operations.push l E o f).obj M))).mp
  simpa only [Category.assoc, Iso.hom_inv_id_app_assoc] using
    ((o.evaluation f).counit m M).symm

private theorem intrinsic_compositor (o : Operations l E)
    (c : Compositors l E o) (m : ℕ)
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (M : System l E X) :
    (coefficientSequenceDerivedEvaluation l E Z m).map ((c.pushComp l E f g).hom.app M) ≫
        ((o.evaluation (f ≫ g)).evaluation m).hom.app M =
      ((o.evaluation g).evaluation m).hom.app ((Operations.push l E o f).obj M) ≫
        (proEtaleConstantDerivedDirectImage g
          (Padic.coefficientExtensionRing l E (m + 1))).map
            (((o.evaluation f).evaluation m).hom.app M) ≫
        (conjugateIsoEquiv ((finiteAdj l E g m).comp (finiteAdj l E f m))
          (finiteAdj l E (f ≫ g) m)
          (sfIntrinsicDerivedPullbackComp (Padic.coefficientExtensionRing l E (m + 1))
            f g)).hom.app ((coefficientSequenceDerivedEvaluation l E X m).obj M) := by
  let ag := (o.direct g).adj
  let af := (o.direct f).adj
  let adjt := (o.direct (f ≫ g)).adj
  let bg := finiteAdj l E g m
  let bf := finiteAdj l E f m
  let bt := finiteAdj l E (f ≫ g) m
  let q := sfIntrinsicDerivedPullbackComp
    (Padic.coefficientExtensionRing l E (m + 1)) f g
  let sg := TwoSquare.mk _ _ _ _ (pullbackTensorDerivedEvaluation l E g m).inv
  let sf := TwoSquare.mk _ _ _ _ (pullbackTensorDerivedEvaluation l E f m).inv
  let st := TwoSquare.mk _ _ _ _ (pullbackTensorDerivedEvaluation l E (f ≫ g) m).inv
  have hs : st.whiskerLeft (c.pullComp f g).hom =
      (sg ≫ᵥ sf).whiskerRight q.hom := by
    ext N
    dsimp only [st, sg, sf, TwoSquare.whiskerLeft, TwoSquare.whiskerRight,
      TwoSquare.vComp, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app]
    simp only [Category.id_comp, Category.comp_id]
    have h := systemPullbackCompositorEvaluation l E o c f g m N
    have hi :
        (coefficientSequenceDerivedEvaluation l E X m).mapIso
            ((c.pullComp f g).symm.app N) ≪≫
          (pullbackTensorDerivedEvaluation l E (f ≫ g) m).app N =
        (pullbackTensorDerivedEvaluation l E f m).app ((pull l E g).obj N) ≪≫
          (finiteDerivedPullback l E m f).mapIso
            ((pullbackTensorDerivedEvaluation l E g m).app N) ≪≫
          q.symm.app ((coefficientSequenceDerivedEvaluation l E Z m).obj N) := by
      apply Iso.ext
      exact h
    simpa only [Iso.trans_inv, Iso.app_inv, Iso.symm_inv, Functor.mapIso_inv,
      Category.assoc] using congrArg Iso.inv hi
  have hm := congrArg (fun s ↦ (mateEquiv (ag.comp af) bt s).natTrans) hs
  rw [conjugateEquiv_mateEquiv_vcomp (ag.comp af) adjt bt,
    mateEquiv_conjugateEquiv_vcomp (ag.comp af) (bg.comp bf) bt,
    mateEquiv_hcomp ag bg af bf] at hm
  have hmM := congr_app hm M
  simpa only [st, sg, sf, ag, af, adjt, bg, bf, bt, q, Compositors.pushComp,
    conjugateIsoEquiv_apply_hom, TwoSquare.whiskerTop, TwoSquare.whiskerBottom,
    TwoSquare.hComp, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id, evaluation_is_mate, Category.assoc] using hmM

private theorem presentation_cancel
    {A B : Type*} [Category A] [Category B] (R : A ≌ B)
    {X : B} {Y : A} (a : X ⟶ R.functor.obj Y) :
    (R.counitIso.app X).inv ≫
        R.functor.map (R.inverse.map a ≫ (R.unitIso.app Y).inv) = a := by
  have hn := R.counitIso.inv.naturality a
  dsimp only [Functor.comp_map, Functor.id_map] at hn
  simp only [Iso.app_inv]
  rw [Functor.map_comp, ← Category.assoc, ← hn, Category.assoc,
    R.counitIso_functor_comp]
  exact Category.comp_id a

private theorem paste_coordinate
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    (R : A ≌ B) (G : B ⥤ C) (F : A ⥤ D) (V : D ⥤ C)
    (ν : R.functor ⋙ G ≅ F ⋙ V) {X : B} {Y : A} (a : X ⟶ R.functor.obj Y) :
    G.map a ≫ ν.hom.app Y =
      G.map (R.counitIso.app X).inv ≫ ν.hom.app (R.inverse.obj X) ≫
        V.map (F.map (R.inverse.map a ≫ (R.unitIso.app Y).inv)) := by
  let b := R.inverse.map a ≫ (R.unitIso.app Y).inv
  have hn := ν.hom.naturality b
  dsimp only [Functor.comp_map] at hn
  rw [← hn, ← Category.assoc, ← G.map_comp]
  rw [presentation_cancel]
  rfl

private theorem compositor_coordinate
    {C₁ C₂ C₃ D₁ D₂ D₃ : Type*}
    [Category C₁] [Category C₂] [Category C₃]
    [Category D₁] [Category D₂] [Category D₃]
    (R₁ : C₁ ≌ D₁) (R₂ : C₂ ≌ D₂) (R₃ : C₃ ≌ D₃)
    (F₁ : C₁ ⥤ C₂) (F₂ : C₂ ⥤ C₃) (F₁₂ : C₁ ⥤ C₃)
    (G₁ : D₁ ⥤ D₂) (G₂ : D₂ ⥤ D₃) (G₁₂ : D₁ ⥤ D₃)
    (ν₁ : R₁.functor ⋙ G₁ ≅ F₁ ⋙ R₂.functor)
    (ν₂ : R₂.functor ⋙ G₂ ≅ F₂ ⋙ R₃.functor)
    (ν₁₂ : R₁.functor ⋙ G₁₂ ≅ F₁₂ ⋙ R₃.functor)
    (α : G₁ ⋙ G₂ ≅ G₁₂) (β : F₁ ⋙ F₂ ≅ F₁₂)
    (X : D₁) (Y : D₂) (Z T : D₃) (p : Z ⟶ T)
    (e₁ : Y ⟶ G₁.obj X) (e₂ : Z ⟶ G₂.obj Y) (e₁₂ : T ⟶ G₁₂.obj X)
    (h₁ : p ≫ e₁₂ = e₂ ≫ G₂.map e₁ ≫ α.hom.app X)
    (h₂ : G₂.map (ν₁.hom.app (R₁.inverse.obj X)) ≫
        ν₂.hom.app (F₁.obj (R₁.inverse.obj X)) ≫
          R₃.functor.map (β.hom.app (R₁.inverse.obj X)) =
      α.hom.app (R₁.functor.obj (R₁.inverse.obj X)) ≫
        ν₁₂.hom.app (R₁.inverse.obj X)) :
    p ≫ (e₁₂ ≫ G₁₂.map (R₁.counitIso.app X).inv ≫
      ν₁₂.hom.app (R₁.inverse.obj X)) =
    (e₂ ≫ G₂.map (R₂.counitIso.app Y).inv ≫ ν₂.hom.app (R₂.inverse.obj Y)) ≫
      R₃.functor.map (F₂.map
        (R₂.inverse.map (e₁ ≫ G₁.map (R₁.counitIso.app X).inv ≫
          ν₁.hom.app (R₁.inverse.obj X)) ≫
            (R₂.unitIso.app (F₁.obj (R₁.inverse.obj X))).inv)) ≫
      R₃.functor.map (β.hom.app (R₁.inverse.obj X)) := by
  let a := e₁ ≫ G₁.map (R₁.counitIso.app X).inv ≫ ν₁.hom.app (R₁.inverse.obj X)
  have hn := α.hom.naturality (R₁.counitIso.app X).inv
  dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at hn
  calc
    _ = e₂ ≫ G₂.map a ≫ ν₂.hom.app (F₁.obj (R₁.inverse.obj X)) ≫
        R₃.functor.map (β.hom.app (R₁.inverse.obj X)) := by
      dsimp only [a]
      rw [← Category.assoc, h₁]
      simp only [Category.assoc]
      rw [← reassoc_of% hn, ← h₂]
      simp only [Functor.map_comp, Category.assoc]
    _ = _ := by
      rw [reassoc_of% (paste_coordinate R₂ G₂ F₂ R₃.functor ν₂ a)]
      simp only [a, Category.assoc]

/-- One evaluated direct-image compositor is the canonical fixed-scalar compositor.
This concerns arbitrary system inputs and composable scheme maps; no open extension,
compact-support comparison, constructibility or finite operation datum occurs.

Source: Stacks 03D8 and 07A7; the compositor factor in the finite-evaluation step of
prop-sf-pf-coherence.proof.md.
(blueprint: lem-sf-system-finite-compositor-coordinates).

Proof: first take t = f ≫ g. The direct evaluations preserve the specified units
and counits. Transpose the displayed square under the finite direct-image
adjunction. The conjugate definition of c.pushComp turns its transpose into the
pullback compositor. Apply systemPullbackCompositorEvaluation, whose ordinary
section and cochain normalizations identify the evaluated pullback compositor.
The canonical coefficient-presentation comparisons have the same section
normalization, and their derived versions are fixed on K-injective
representatives. Hence both transposes are the same map, including their scalar
unit maps; adjunction injectivity gives the square. Finally equality induction on
h supplies the two index transports. Empty schemes and zero inputs use the same
adjunction calculation. -/
theorem compositor (o : Operations l E)
    (c : Compositors l E o) (m : ℕ)
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (t : X ⟶ Z)
    (h : f ≫ g = t) (M : System l E X) :
    let A := ULift.{u + 1} (Padic.coefficientExtensionRing l E (m + 1))
    let RZ := sfIntrinsicDerivedEquivalence Z (Padic.coefficientExtensionRing l E (m + 1))
    (coefficientSequenceDerivedEvaluation l E Z m).map
        ((c.pushComp l E f g).hom.app M ≫
          (eqToIso (congrArg (Operations.push l E o) h)).hom.app M) ≫
      (push l E o m t M).hom =
    (push l E o m g ((Operations.push l E o f).obj M)).hom ≫
      RZ.functor.map ((ProperOpenPush A g).map (fixedPush l E o m f M).hom) ≫
      RZ.functor.map
        ((conjugateIsoEquiv
          ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) g).comp
            (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f))
          (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) (f ≫ g))
          (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) f g)).hom.app
            (input l E m X M) ≫
          (indexIso (ProperOpenPush A) h).hom.app (input l E m X M)) := by
  subst t
  dsimp only
  simp only [congrArg, eqToIso_refl, Iso.refl_hom, NatTrans.id_app,
    indexIso, Category.comp_id]
  let A := Padic.coefficientExtensionRing l E (m + 1)
  let RX := sfIntrinsicDerivedEquivalence X A
  let RY := sfIntrinsicDerivedEquivalence Y A
  let RZ := sfIntrinsicDerivedEquivalence Z A
  let Ff := ProperOpenPush (ULift.{u + 1} A) f
  let Fg := ProperOpenPush (ULift.{u + 1} A) g
  let Ft := ProperOpenPush (ULift.{u + 1} A) (f ≫ g)
  let Gf := proEtaleConstantDerivedDirectImage f A
  let Gg := proEtaleConstantDerivedDirectImage g A
  let Gt := proEtaleConstantDerivedDirectImage (f ≫ g) A
  let α := conjugateIsoEquiv ((finiteAdj l E g m).comp (finiteAdj l E f m))
    (finiteAdj l E (f ≫ g) m) (sfIntrinsicDerivedPullbackComp A f g)
  let β := conjugateIsoEquiv
    ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} (ULift.{u + 1} A)) g).comp
      (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} (ULift.{u + 1} A)) f))
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} (ULift.{u + 1} A)) (f ≫ g))
    (leftDerivedUpperStarComp (ModuleCat.{u + 1} (ULift.{u + 1} A)) f g)
  have h := compositor_coordinate RX RY RZ Ff Fg Ft Gf Gg Gt
    (sfIntrinsicDerivedDirectImageComparison f A)
    (sfIntrinsicDerivedDirectImageComparison g A)
    (sfIntrinsicDerivedDirectImageComparison (f ≫ g) A) α β
    ((coefficientSequenceDerivedEvaluation l E X m).obj M)
    ((coefficientSequenceDerivedEvaluation l E Y m).obj ((Operations.push l E o f).obj M))
    _ _ ((coefficientSequenceDerivedEvaluation l E Z m).map ((c.pushComp l E f g).hom.app M))
    (((o.evaluation f).evaluation m).hom.app M)
    (((o.evaluation g).evaluation m).hom.app ((Operations.push l E o f).obj M))
    (((o.evaluation (f ≫ g)).evaluation m).hom.app M)
    (intrinsic_compositor l E o c m f g M)
    (sfIntrinsicDirectCompositorCoordinates A f g (input l E m X M))
  simpa only [push, fixedPush, input, RX, RY, RZ, Ff, Fg, Ft, Gf, Gg, Gt,
    α, β, A, Iso.trans_hom, Iso.app_hom, Iso.symm_hom, Iso.app_inv,
    Functor.mapIso_hom] using h

end WeilConjectures.IntegralSystemRealization.FiniteCoordinates
