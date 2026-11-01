/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.NativeExceptionalForgetful.NativeExceptionalHomTransport
import WeilConjectures.SixFunctors.NativeExceptionalForgetful.NativeExceptionalOrdinaryMateLift
import WeilConjectures.SixFunctors.NativeExceptionalForgetful.NativeOrdinaryConeDetection
import WeilConjectures.SixFunctors.NativeGeometricBrown.NativeGeometricBrownConstructibleComparison
import WeilConjectures.SixFunctors.LocallyFiniteAdicCompactSupport.CompactSupportStageActionAdjunction
import WeilConjectures.CategoryTheory.Shift.AdjunctionHomEquiv

/-! # Graded ordinary exceptional counit bijections

Source: current blueprint, cor-coef-verdier-weil-equivariance.proof.md,
exceptional-adjunction sentence, graded Hom step.
(blueprint: lem-sf-native-exceptional-ordinary-counit-graded).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory.Endofunctor.IsoAlgebra
open WeilConjectures.AdicQbarRealization

namespace WeilConjectures.NativeExceptionalForgetful
variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] [Fact (l ≠ D.p)]

private theorem ordinary_adjunction {X Y : Space D} (f₀ : X.base ⟶ Y.base)
    [IsSeparated f₀.left] [LocallyOfFiniteType f₀.left] [QuasiCompact f₀.left] :
    ∃ (h : ∀ K, ordinaryCounitProperty D l X K →
      ordinaryCounitProperty D l Y ((counitOrdinaryShriek D l f₀).obj K))
      (G : (ordinaryCounitProperty D l Y).FullSubcategory ⥤
        (ordinaryCounitProperty D l X).FullSubcategory),
      Nonempty (ordinaryCounitLeft D l f₀ h ⊣ G) := by
  classical
  let c := counitCompactification D f₀
  let := Compactification.over (k₀ := D.k₀) c
  let Xb := (X.base.left ↘ Spec (CommRingCat.of D.k₀)).geometricFiber
  let Yb := (Y.base.left ↘ Spec (CommRingCat.of D.k₀)).geometricFiber
  let Zb := (c.Z ↘ Spec (CommRingCat.of D.k₀)).geometricFiber
  let fb := Scheme.Hom.geometricFiberMap f₀.left (comp_over f₀.left (Spec (.of D.k₀)))
  let ib := Scheme.Hom.geometricFiberMap c.i (comp_over c.i (Spec (.of D.k₀)))
  let pb := Scheme.Hom.geometricFiberMap c.g (comp_over c.g (Spec (.of D.k₀)))
  have : IsProper pb :=
    Scheme.Hom.geometricFiberMap_of_isStableUnderBaseChange
      (P := @IsProper) c.g (comp_over c.g _) inferInstance
  let cb : Compactification fb :=
    { Z := Zb, g := pb, i := ib
      comm := by
        dsimp [fb, ib, pb]
        rw [← Scheme.Hom.geometricFiberMap_comp]
        congr 1
        exact c.comm
      isProper := inferInstance
      isOpenImmersion := inferInstance }
  let : Xb.Over (Spec (CommRingCat.of (AlgebraicClosure D.k₀))) :=
    ⟨(X.base.left ↘ Spec (CommRingCat.of D.k₀)).geometricFiberToAlgebraicClosure⟩
  let : Yb.Over (Spec (CommRingCat.of (AlgebraicClosure D.k₀))) :=
    ⟨(Y.base.left ↘ Spec (CommRingCat.of D.k₀)).geometricFiberToAlgebraicClosure⟩
  let : fb.IsOver (Spec (CommRingCat.of (AlgebraicClosure D.k₀))) :=
    ⟨Scheme.Hom.geometricFiberMap_comp_geometricFiberToAlgebraicClosure f₀.left _⟩
  have : LocallyOfFiniteType (Xb ↘ Spec (CommRingCat.of (AlgebraicClosure D.k₀))) := by
    change LocallyOfFiniteType
      (X.base.left ↘ Spec (CommRingCat.of D.k₀)).geometricFiberToAlgebraicClosure
    infer_instance
  have : QuasiCompact (Xb ↘ Spec (CommRingCat.of (AlgebraicClosure D.k₀))) := by
    change QuasiCompact (X.base.left ↘ Spec (CommRingCat.of D.k₀)).geometricFiberToAlgebraicClosure
    infer_instance
  have : LocallyOfFiniteType (Yb ↘ Spec (CommRingCat.of (AlgebraicClosure D.k₀))) := by
    change LocallyOfFiniteType
      (Y.base.left ↘ Spec (CommRingCat.of D.k₀)).geometricFiberToAlgebraicClosure
    infer_instance
  have : QuasiCompact (Yb ↘ Spec (CommRingCat.of (AlgebraicClosure D.k₀))) := by
    change QuasiCompact (Y.base.left ↘ Spec (CommRingCat.of D.k₀)).geometricFiberToAlgebraicClosure
    infer_instance
  let D' : FiniteFieldDatum.{u} :=
    { D with
      k := AlgebraicClosure D.k₀
      field_closure := inferInstance
      algebra_closure := inferInstance
      isAlgClosure := inferInstance }
  obtain ⟨P⟩ := ConstructibleExceptionalCoefficients.exists_coefficient_construction
    l (ULift.{u} (PadicAlgCl l)) D' (Fact.out : l ≠ D.p) fb
  obtain ⟨N, ⟨C⟩⟩ :=
    LocallyFiniteAdicCompactSupport.locally_finite_adic_compact_support_realization
      l D' (Fact.out : l ≠ D.p) P cb
  have := LocallyFiniteAdicCompactSupport.compactSupport_stageAction_isLeftAdjoint
    l D' (Fact.out : l ≠ D.p) P cb C.stage
  let Fs := C.stage.system.functor
  let Gs := Fs.rightAdjoint
  let stageAdj : Fs ⊣ Gs := Adjunction.ofIsLeftAdjoint Fs
  obtain ⟨adj, _⟩ :=
    NativeGeometricBrown.native_geometric_brown_constructible_comparison
      D.k₀ l f₀.left C.source C.target Fs Gs stageAdj C.alpha
  exact ⟨NativeGeometricBrown.preserves_constructible D.k₀ l f₀.left
    C.source C.target Fs C.alpha, _, ⟨adj⟩⟩

private theorem shifted_counit_bijective
    {A B : Type*} [Category A] [Category B] [HasShift A ℤ] [HasShift B ℤ]
    (F : A ⥤ B) [F.CommShift ℤ] (G : B ⥤ A) (adj : F ⊣ G)
    (K H : A) (L : B) (q : H ≅ G.obj L) (r : ℤ) :
    Function.Bijective (fun v : K ⟶ H⟦r⟧ ↦
      F.map v ≫ (F.commShiftIso r).hom.app H ≫
        (F.map q.hom ≫ adj.counit.app L)⟦r⟧') := by
  let e := (Iso.homCongr (Iso.refl K) ((shiftFunctor A r).mapIso q)).trans
    (adj.shiftedHomEquiv r K L)
  convert e.bijective using 1 <;> try rfl
  funext v
  simp only [e, Equiv.trans_apply, Iso.homCongr_apply, Iso.refl_inv,
    Category.id_comp, Functor.mapIso_hom, Adjunction.shiftedHomEquiv_apply,
    Functor.map_comp, Functor.commShiftIso_hom_naturality_assoc,
    Category.assoc]

private theorem ordinary_graded_bijective
    {A B : Type*} [Category A] [Category B] [HasShift A ℤ] [HasShift B ℤ]
    (P : ObjectProperty A) [P.IsStableUnderShift ℤ]
    (Q : ObjectProperty B) [Q.IsStableUnderShift ℤ]
    (F : A ⥤ B) [F.CommShift ℤ] (h : ∀ K, P K → Q (F.obj K))
    (G : Q.FullSubcategory ⥤ P.FullSubcategory)
    (adj : P.liftFullSubcategory Q F h ⊣ G)
    (K H : P.FullSubcategory) (L : Q.FullSubcategory)
    (K' H' : B) (cK : K' ≅ F.obj K.obj) (cH : H' ≅ F.obj H.obj)
    (t : H' ⟶ L.obj)
    (ht : IsIso (adj.homEquiv H L (ObjectProperty.homMk (cH.inv ≫ t)))) (r : ℤ) :
    Function.Bijective (fun v : K.obj ⟶ H.obj⟦r⟧ ↦
      cK.hom ≫ F.map v ≫ (F.commShiftIso r).hom.app H.obj ≫ cH.inv⟦r⟧' ≫ t⟦r⟧') := by
  let V := P.liftFullSubcategory Q F h
  let w : V.obj H ⟶ L := ObjectProperty.homMk (cH.inv ≫ t)
  let q : H ≅ G.obj L := asIso (adj.homEquiv H L w)
  have hq : V.map q.hom ≫ adj.counit.app L = w := by
    exact (adj.homEquiv_counit (g := adj.homEquiv H L w)).symm.trans
      ((adj.homEquiv H L).symm_apply_apply w)
  have hh := shifted_counit_bijective V G adj K H L q r
  rw [hq] at hh
  let s : (K ⟶ H⟦r⟧) ≃ (K.obj ⟶ H.obj⟦r⟧) :=
    P.fullyFaithfulι.homEquiv.trans
      (Iso.homCongr (Iso.refl _) ((P.ι.commShiftIso r).app H))
  let z : (V.obj K ⟶ L⟦r⟧) ≃ (K' ⟶ L.obj⟦r⟧) :=
    Q.fullyFaithfulι.homEquiv.trans
      (Iso.homCongr cK.symm ((Q.ι.commShiftIso r).app L))
  have hs (v : K.obj ⟶ H.obj⟦r⟧) :
      s.symm v = ObjectProperty.homMk (v ≫ (P.ι.commShiftIso r).inv.app H) := by
    apply s.symm_apply_eq.mpr
    symm
    simp only [s, Equiv.trans_apply, Iso.homCongr_apply,
      Functor.FullyFaithful.homEquiv_apply, Iso.refl_inv]
    simp
  have hc : Q.ι.map ((V.commShiftIso r).hom.app H) ≫
      (Q.ι.commShiftIso r).hom.app (V.obj H) =
      F.map ((P.ι.commShiftIso r).hom.app H) ≫ (F.commShiftIso r).hom.app H.obj := by
    simpa [Functor.commShiftIso_comp_hom_app,
      ObjectProperty.liftFullSubcategoryCompιIso] using
      (NatTrans.shift_app_comm
        (P.liftFullSubcategoryCompιIso Q F h).hom r H)
  convert (z.bijective.comp hh).comp s.symm.bijective using 1
  try rfl
  funext v
  simp only [Function.comp_apply, z, Equiv.trans_apply, Iso.homCongr_apply,
    Iso.symm_inv, Functor.FullyFaithful.homEquiv_apply, Functor.map_comp,
    Category.assoc]
  rw [hs]
  change _ = cK.hom ≫ F.map (v ≫ (P.ι.commShiftIso r).inv.app H) ≫
    Q.ι.map ((V.commShiftIso r).hom.app H) ≫
    Q.ι.map (w⟦r⟧') ≫ (Q.ι.commShiftIso r).hom.app L
  erw [Q.ι.commShiftIso_hom_naturality w r]
  erw [← Category.assoc (Q.ι.map _), hc]
  simp [w, Functor.map_comp, Category.assoc, ← F.map_comp_assoc]

/--
Postcomposition by the fixed ordinary counit carrier is bijective in every
graded ordinary Hom degree.

Proof source: cor-coef-verdier-weil-equivariance.proof.md, final exceptional-
adjunction sentence. Construct the restricted ordinary adjunction by transporting
the common-stage adjunction. Realize the invariant ordinary transpose as a native
map q:H -> M. If a native v:K -> H has ordinary composite vq zero, ordinary
adjunction naturality makes nativeShriek(v) followed by t zero after forgetting.
The carrier equation, faithfulness of rho, and naturality of a give VX(v) followed
by e zero; cancel e. The cone-detection criterion and the common-stage isomorphism
VX(H) -> VX(M) make the ordinary map of q invertible. Its composite with the
right-object comparison is therefore an invertible ordinary transpose. Compose
its shifted Hom isomorphism with Adjunction.shiftedHomEquiv and transport through
the full-subcategory shift comparisons to obtain the displayed map. Naturality
of a is used only on native morphisms; native forgetting is never assumed faithful.
(blueprint: lem-sf-native-exceptional-ordinary-counit-graded).
-/
theorem native_exceptional_ordinary_counit_graded (R : Family l D)
    (X Y : Space D) (VX : ForgetModel D l R X) (VY : ForgetModel D l R Y)
    (f₀ : X.base ⟶ Y.base)
    [IsSeparated f₀.left] [LocallyOfFiniteType f₀.left] [QuasiCompact f₀.left]
    (S : CoefficientSystem D l f₀) (c : Compactification (geometricMap D f₀))
    (a : nativeShriek D l f₀ ⋙ VY.functor ≅
      VX.functor ⋙ (S.ring.operation c .closed).F)
    (L : W D l Y) (H : W D l X)
    (e : VX.functor.obj H ≅ (S.ring.operation c .closed).G.obj (VY.functor.obj L))
    (t : WeilComplex.forget.obj ((nativeShriek D l f₀).obj H) ⟶
      WeilComplex.forget.obj L)
    (ht : ((ProEtale.adicLowerStar l (closureMap D Y)).rightDerivedFunctor ⋙
      sectionDerived l (geometric D Y).base.left
        (R.data (geometric D Y)).realization).map t =
      VY.realization.inv.app ((nativeShriek D l f₀).obj H) ≫
        (rho D l R Y).map (a.hom.app H ≫ (S.ring.operation c .closed).F.map e.hom ≫
          (S.ring.operation c .closed).adjunction.counit.app (VY.functor.obj L)) ≫
        VY.realization.hom.app L)
    (hinv : (t ≫ (shiftFunctorZero _ ℤ).inv.app (WeilComplex.forget.obj L)) ∈
      CyclicDerivedHomInvariants (WeilSheaf.frobeniusPullback D.k₀ l Y.base.left)
        ((nativeShriek D l f₀).obj H).obj L.obj) :
    ∀ (K : W D l X) (r : ℤ), Function.Bijective
      (fun v : CyclicDerivedHom (WeilSheaf.frobeniusPullback D.k₀ l X.base.left)
        K.obj H.obj r ↦ counitHomTransport D l f₀ K H r v ≫ t⟦r⟧') := by
  obtain ⟨h, G, ⟨adj⟩⟩ := ordinary_adjunction D l f₀
  obtain ⟨M, b, d, q, hq⟩ := native_exceptional_ordinary_mate_lift
    D l R X Y VX VY f₀ h G adj S c L H t hinv
  let : G.IsRightAdjoint := ⟨_, ⟨adj⟩⟩
  let V := ordinaryCounitLeft D l f₀ h
  let w : V.obj (ordinaryCounitObject D l X H) ⟶ ordinaryCounitObject D l Y L :=
    ObjectProperty.homMk ((counitForgetComparison D l f₀).inv.app H ≫ t)
  let q' : ordinaryCounitObject D l X H ⟶ ordinaryCounitObject D l X M :=
    ObjectProperty.homMk (WeilComplex.forget.map q)
  have hq' : q' ≫ d.hom = adj.homEquiv _ _ w := hq
  let : (rho D l R Y).CommShift ℤ := (R.data (geometric D Y)).shift
  let : (rho D l R Y).IsTriangulated := (R.data (geometric D Y)).exact
  let : (S.ring.operation c .closed).F.Additive :=
    (S.ring.operation c .closed).leftAdditive
  have hdetect : ∀ (K : W D l X) (v : K ⟶ H),
      WeilComplex.forget.map (v ≫ q) = 0 → VX.functor.map v = 0 := by
    intro K v hv
    let v' : ordinaryCounitObject D l X K ⟶ ordinaryCounitObject D l X H :=
      ObjectProperty.homMk (WeilComplex.forget.map v)
    have hleft : V.map v' ≫ w = 0 := by
      apply (adj.homEquiv _ _).injective
      rw [adj.homEquiv_naturality_left]
      rw [← hq']
      have hcomp : v' ≫ q' = 0 := by
        apply ObjectProperty.hom_ext
        change WeilComplex.forget.map v ≫ WeilComplex.forget.map q = 0
        simpa only [Functor.map_comp] using hv
      rw [← Category.assoc, hcomp, zero_comp]
      simp [Adjunction.homEquiv_unit]
    have hleft' : (counitOrdinaryShriek D l f₀).map (WeilComplex.forget.map v) ≫
        (counitForgetComparison D l f₀).inv.app H ≫ t = 0 := by
      exact congrArg (fun z ↦ z.hom) hleft
    have hnative : WeilComplex.forget.map ((nativeShriek D l f₀).map v) ≫ t = 0 := by
      have hn := (counitForgetComparison D l f₀).inv.naturality v
      dsimp only [Functor.comp_map] at hn
      apply (cancel_epi ((counitForgetComparison D l f₀).inv.app K)).1
      rw [comp_zero]
      calc
        _ = (counitOrdinaryShriek D l f₀).map (WeilComplex.forget.map v) ≫
            (counitForgetComparison D l f₀).inv.app H ≫ t :=
          ((reassoc_of% hn) t).symm
        _ = 0 := hleft'
    let T : DerivedCategory (ProEtale.AdicSheaf l
        (Y.base.left ↘ Spec (CommRingCat.of D.k₀)).geometricFiber) ⥤
        DerivedCategory (modules l (geometric D Y).base.left
          (R.data (geometric D Y)).realization) :=
      (ProEtale.adicLowerStar l (closureMap D Y)).rightDerivedFunctor ⋙
        sectionDerived l (geometric D Y).base.left (R.data (geometric D Y)).realization
    let : T.PreservesZeroMorphisms := by
      dsimp [T, sectionDerived]
      infer_instance
    let g := a.hom.app H ≫ (S.ring.operation c .closed).F.map e.hom ≫
      (S.ring.operation c .closed).adjunction.counit.app (VY.functor.obj L)
    have heq : VY.realization.hom.app ((nativeShriek D l f₀).obj H) ≫ T.map t =
        (rho D l R Y).map g ≫ VY.realization.hom.app L := by
      rw [ht]
      simp [g]
    have hn : (rho D l R Y).map (VY.functor.map ((nativeShriek D l f₀).map v)) ≫
        VY.realization.hom.app ((nativeShriek D l f₀).obj H) =
        VY.realization.hom.app ((nativeShriek D l f₀).obj K) ≫
          T.map (WeilComplex.forget.map ((nativeShriek D l f₀).map v)) :=
      VY.realization.hom.naturality ((nativeShriek D l f₀).map v)
    let ff : (rho D l R Y).FullyFaithful := Classical.choice
      ((Functor.FullyFaithful.nonempty_iff_map_bijective _).mpr
        (R.data (geometric D Y)).fully_faithful)
    have hscalar : VY.functor.map ((nativeShriek D l f₀).map v) ≫ g = 0 := by
      apply ff.map_injective
      apply (cancel_mono (VY.realization.hom.app L)).1
      simp only [Functor.map_zero, zero_comp]
      calc
        _ = (rho D l R Y).map (VY.functor.map ((nativeShriek D l f₀).map v)) ≫
            (VY.realization.hom.app ((nativeShriek D l f₀).obj H) ≫ T.map t) := by
          rw [heq, Functor.map_comp, Category.assoc]
        _ = VY.realization.hom.app ((nativeShriek D l f₀).obj K) ≫
            T.map (WeilComplex.forget.map ((nativeShriek D l f₀).map v) ≫ t) := by
          rw [Functor.map_comp, ← Category.assoc, hn, Category.assoc]
        _ = 0 := by rw [hnative, Functor.map_zero, comp_zero]
    have han : VY.functor.map ((nativeShriek D l f₀).map v) ≫ a.hom.app H =
        a.hom.app K ≫ (S.ring.operation c .closed).F.map (VX.functor.map v) :=
      a.hom.naturality v
    have hstage : (S.ring.operation c .closed).F.map (VX.functor.map v ≫ e.hom) ≫
        (S.ring.operation c .closed).adjunction.counit.app (VY.functor.obj L) = 0 := by
      apply (cancel_epi (a.hom.app K)).1
      simpa only [g, Functor.map_comp, Category.assoc, reassoc_of% han,
        comp_zero] using hscalar
    have hz : VX.functor.map v ≫ e.hom = 0 := by
      apply ((S.ring.operation c .closed).adjunction.homEquiv _ _).symm.injective
      simpa only [Adjunction.homEquiv_counit, Functor.map_zero, zero_comp] using hstage
    apply (cancel_mono e.hom).1
    simpa only [zero_comp] using hz
  have hqi := native_ordinary_cone_detection D l R X VX H M q
    ⟨e ≪≫ b.symm⟩ hdetect
  let := hqi
  have hmate : IsIso (adj.homEquiv (ordinaryCounitObject D l X H)
      (ordinaryCounitObject D l Y L) w) := by
    rw [← hq']
    have : IsIso ((ordinaryCounitProperty D l X).ι.map q') := by
      change IsIso (WeilComplex.forget.map q)
      exact hqi
    have : IsIso q' := isIso_of_reflects_iso _ (ordinaryCounitProperty D l X).ι
    infer_instance
  intro K r
  let : (ordinaryCounitProperty D l X).IsStableUnderShift ℤ := by
    dsimp [ordinaryCounitProperty, ProEtale.DerivedCategory.boundedAdicConstructible]
    infer_instance
  let : (ordinaryCounitProperty D l Y).IsStableUnderShift ℤ := by
    dsimp [ordinaryCounitProperty, ProEtale.DerivedCategory.boundedAdicConstructible]
    infer_instance
  simpa only [counitHomTransport, Category.assoc, WeilComplex.forget,
    CyclicDerivedHom, Iso.app_hom, Iso.app_inv, Functor.comp_obj,
    ObjectProperty.ι_obj] using ordinary_graded_bijective
    (ordinaryCounitProperty D l X) (ordinaryCounitProperty D l Y)
    (counitOrdinaryShriek D l f₀) h G adj
    (ordinaryCounitObject D l X K) (ordinaryCounitObject D l X H)
    (ordinaryCounitObject D l Y L) _ _
    ((counitForgetComparison D l f₀).app K)
    ((counitForgetComparison D l f₀).app H) t hmate r

end WeilConjectures.NativeExceptionalForgetful
