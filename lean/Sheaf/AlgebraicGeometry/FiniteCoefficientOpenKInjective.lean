/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K5
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleConstantExact
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Sheaf.AlgebraicGeometry.FiniteCoefficientOpenRestriction
import Sheaf.Algebra.Homology.KInjectiveRestrictLocalized
import Mathlib.CategoryTheory.Sites.CoverLifting

/-!
# Open finite-ring pullback preserves K-injectivity

Source: Stacks Project, Tags 03CE, 04IX and 03D3.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale

private theorem pushforward_of_ringIso_isEquivalence
    {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (e : C ≌ D) [e.inverse.IsDenseSubsite K J]
    (R : Sheaf J RingCat.{u + 1}) (S : Sheaf K RingCat.{u + 1})
    (c : S ≅ (e.inverse.sheafPushforwardContinuous RingCat.{u + 1} K J).obj R) :
    (SheafOfModules.pushforward.{u + 1} (F := e.inverse) c.hom).IsEquivalence := by
  let ψ : R ⟶ (e.functor.sheafPushforwardContinuous RingCat.{u + 1} J K).obj S :=
    { hom := Functor.whiskerRight e.op.unitIso.hom R.obj ≫
        Functor.whiskerLeft e.functor.op c.inv.hom }
  have H₁ : Functor.whiskerRight (NatTrans.op e.symm.counit) R.obj =
      ψ.hom ≫ e.functor.op.whiskerLeft c.hom.hom := by
    apply NatTrans.ext
    funext U
    change R.obj.map _ =
      (R.obj.map _ ≫ c.inv.hom.app _) ≫ c.hom.hom.app _
    rw [Category.assoc]
    have hc := congrArg (fun f ↦ f.hom.app (e.functor.op.obj U)) c.inv_hom_id
    have hc' : c.inv.hom.app (e.functor.op.obj U) ≫
        c.hom.hom.app (e.functor.op.obj U) = 𝟙 _ := hc
    change R.obj.map (e.unitInv.app U.unop).op =
      R.obj.map (e.unitInv.app U.unop).op ≫
        (c.inv.hom.app (e.functor.op.obj U) ≫ c.hom.hom.app (e.functor.op.obj U))
    exact (Category.comp_id _).symm.trans
      (congrArg (fun f ↦ R.obj.map (e.unitInv.app U.unop).op ≫ f) hc'.symm)
  have H₂ : c.hom.hom ≫ e.inverse.op.whiskerLeft ψ.hom ≫
      Functor.whiskerRight (NatTrans.op e.symm.unit) S.obj = 𝟙 S.obj := by
    apply NatTrans.ext
    funext U
    change c.hom.hom.app U ≫
      (R.obj.map (e.unitInv.app (e.inverse.obj U.unop)).op ≫
        c.inv.hom.app (e.functor.op.obj (e.inverse.op.obj U))) ≫
        S.obj.map (e.counitInv.app U.unop).op = 𝟙 _
    rw [Category.assoc]
    have hn := c.inv.hom.naturality (e.counitInv.app U.unop).op
    change R.obj.map (e.inverse.map (e.counitInv.app U.unop)).op ≫
      c.inv.hom.app U =
      c.inv.hom.app (e.functor.op.obj (e.inverse.op.obj U)) ≫
        S.obj.map (e.counitInv.app U.unop).op at hn
    rw [← hn]
    have hm : R.obj.map (e.unitInv.app (e.inverse.obj U.unop)).op ≫
        R.obj.map (e.inverse.map (e.counitInv.app U.unop)).op = 𝟙 _ := by
      rw [← Functor.map_comp, ← op_comp]
      simp
    rw [← Category.assoc (R.obj.map _) (R.obj.map _) _, hm]
    change c.hom.hom.app U ≫ 𝟙 _ ≫ c.inv.hom.app U = 𝟙 _
    have hc : c.hom.hom.app U ≫ c.inv.hom.app U = 𝟙 _ :=
      congrArg (fun f ↦ f.hom.app U) c.hom_inv_id
    exact (congrArg (fun f ↦ c.hom.hom.app U ≫ f)
      (Category.id_comp (c.inv.hom.app U))).trans hc
  have : e.symm.functor.IsContinuous K J := inferInstanceAs (e.inverse.IsContinuous K J)
  have : e.symm.inverse.IsContinuous J K := inferInstanceAs (e.functor.IsContinuous J K)
  exact inferInstanceAs
    (SheafOfModules.pushforwardPushforwardEquivalence e.symm c.hom ψ H₁ H₂).functor.IsEquivalence

/-- Restriction along an open immersion preserves K-injective finite-ring module complexes.

Source: Stacks Project, Tag 08FI; step 4 of lem-exc-proetale-open-derived-image.
(blueprint: lem-exc-finite-coefficient-open-kinjective)

Proof: identify the actual transported module pullback with slice restriction using
the initial-pair Kan comparison and coefficient sheafification comparison of steps
1--2 of the parent. Restriction to the slice preserves K-injectivity by
lem-pur-kinjective-restrict-localized: its left adjoint is exact extension by zero.
Transport the resulting complex across the equivalence of slice sites and their
coefficient rings. These additive equivalences preserve acyclicity and homotopies,
so preserve K-injectivity. The natural comparison with actual pullback induces an
isomorphism of complexes, along which K-injectivity is invariant. No boundedness,
commutativity, or termwise injectivity assumption is used. -/
theorem finiteCoefficientOpenPullback_isKInjective {U T : Scheme.{u}} (j : U ⟶ T)
    [IsOpenImmersion j] (A : Type (u + 1))
    [Ring A] [Finite A] [TopologicalSpace A] [DiscreteTopology A]
    (I : CochainComplex (FiniteCoefficientModules T A) ℤ) [I.IsKInjective] :
    CochainComplex.IsKInjective
      (((finiteCoefficientModulePullback j A).mapHomologicalComplex (.up ℤ)).obj I) := by
  classical
  obtain ⟨d, hd, rho, hlinear, hsite, hmodule, hadd, adj, hunit, hrestriction⟩ :=
    finiteCoefficientOpenRestriction j A
  let W : T.ProEt := Scheme.ProEt.mk j
  let e := Scheme.ProEt.sliceEquiv T W
  let : e.inverse.IsDenseSubsite (Scheme.ProEt.topology U)
      ((Scheme.ProEt.topology T).over W) := Scheme.ProEt.sliceDense T W
  let c : finiteCoefficientRingSheaf U A ≅
      (e.inverse.sheafPushforwardContinuous RingCat.{u + 1}
        (Scheme.ProEt.topology U) ((Scheme.ProEt.topology T).over W)).obj
          ((finiteCoefficientRingSheaf T A).over W) :=
    (fullyFaithfulSheafToPresheaf _ _).preimageIso d
  let P := SheafOfModules.pushforward.{u + 1} (F := e.inverse) c.hom
  let R := SheafOfModules.overFunctor.{u + 1} (finiteCoefficientRingSheaf T A) W
  let : P.IsEquivalence := pushforward_of_ringIso_isEquivalence _ _ e _ _ c
  let : P.Additive := P.additive_of_preserves_binary_products
  let : R.PreservesZeroMorphisms := ⟨by intros; ext V x; rfl⟩
  let : R.Additive := ⟨by intros; ext V x; rfl⟩
  have hKI : CochainComplex.IsKInjective
      ((R.mapHomologicalComplex (.up ℤ)).obj I) :=
    isKInjective_restrict_localized (finiteCoefficientRingSheaf T A) W inferInstance I
  let := hKI
  have hP : CochainComplex.IsKInjective
      ((P.mapHomologicalComplex (.up ℤ)).obj
        ((R.mapHomologicalComplex (.up ℤ)).obj I)) := inferInstance
  let S := R ⋙ P
  let hc (N : FiniteCoefficientModules T A) :
      ((finiteCoefficientModulePullback j A).obj N) ≅ S.obj N := by
    apply (SheafOfModules.fullyFaithfulForget _).preimageIso
    refine PresheafOfModules.isoMk (fun V ↦ ?_) ?_
    · refine ModuleCat.isoMk (rho N V.unop).toAddCommGrpIso ?_
      intro r
      ext m
      exact (hlinear N V.unop r m).symm
    · intro V V' b
      ext m
      exact hsite N V.unop V'.unop b.unop m
  have H : finiteCoefficientModulePullback j A ≅ S :=
    NatIso.ofComponents hc (by
      intro N N' h
      ext V m
      exact hmodule N N' h V.unop m)
  let := hP
  have hS : CochainComplex.IsKInjective ((S.mapHomologicalComplex (.up ℤ)).obj I) := by
    have : CochainComplex.IsKInjective
        ((R.mapHomologicalComplex (.up ℤ) ⋙ P.mapHomologicalComplex (.up ℤ)).obj I) := hP
    exact CochainComplex.isKInjective_of_iso
      ((Functor.mapHomologicalComplexCompIso (Iso.refl S) (.up ℤ)).app I)
  let := hS
  exact CochainComplex.isKInjective_of_iso
    ((NatIso.mapHomologicalComplex H (.up ℤ)).app I).symm


end AlgebraicGeometry.ProEtale
