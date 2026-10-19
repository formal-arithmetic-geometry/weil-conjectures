/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K5
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleConstantExact
public import Sheaf.AlgebraicGeometry.ProEtaleOpenUnitEvaluation
import Mathlib.CategoryTheory.Sites.CoverLifting
import Sheaf.AlgebraicGeometry.ProEtaleFiniteModuleAdjunction

/-!
# Finite-ring open restriction with its normalized unit

Source: Stacks Project, Tags 03CE, 04IX and 03D3.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Open pullback of finite, possibly noncommutative coefficient modules is restriction,
with its scalar action, both naturalities, and the specified Kan unit.

Source: Stacks Project, Tags 03CE, 04IX and 03D3; steps 1--3 of
lem-exc-proetale-open-derived-image.
(blueprint: lem-exc-finite-coefficient-open-restriction)

Proof: composition with the open immersion and base change are adjoint site
functors. Composition is continuous and cocontinuous. Its sheafification comparison
on the continuous-function ring presheaf gives d and fixes constant sections.
Check the ringed-site adjunction equations after precomposing with the sheafification
unit: the first is naturality of that unit and the definition of the direct-image
coefficient map; the second follows from the first and the site triangle identity.
Mathlib's pushforwardPushforwardAdj now makes coefficient restriction left adjoint
to the specified direct image. Compare this left adjoint with the published actual
pullback by leftAdjointUniq, using finiteModuleAdjunction. The components of that
natural module isomorphism give rho, its semilinearity, and both naturalities.
The normalized transpose characterization of finiteModuleAdjunction, applied to
the identity, proves the model-unit equation. Compatibility of units with
leftAdjointUniq and the section formula for pushforwardPushforwardAdj give exactly
restriction along the first projection. No commutativity is used. -/
theorem finiteCoefficientOpenRestriction {U T : Scheme.{u}} (j : U ⟶ T)
    [IsOpenImmersion j] (A : Type (u + 1))
    [Ring A] [Finite A] [TopologicalSpace A] [DiscreteTopology A] :
    ∃ d : (finiteCoefficientRingSheaf U A).obj ≅
        (Scheme.proEtaleOpenComposition j).op ⋙ (finiteCoefficientRingSheaf T A).obj,
      (∀ (W : U.ProEt) (a : A),
        (d.hom.app (op W)) ((finiteCoefficientScalarMap U A).app (op W) a) =
          (finiteCoefficientScalarMap T A).app
            (op ((Scheme.proEtaleOpenComposition j).obj W)) a) ∧
      ∃ rho : ∀ (N : FiniteCoefficientModules T A) (W : U.ProEt),
          ((finiteCoefficientModulePullback j A).obj N).val.obj (op W) ≃+
            N.val.obj (op ((Scheme.proEtaleOpenComposition j).obj W)),
        (∀ (N : FiniteCoefficientModules T A) (W : U.ProEt)
          (r : (finiteCoefficientRingSheaf U A).obj.obj (op W))
          (m : ((finiteCoefficientModulePullback j A).obj N).val.obj (op W)),
          rho N W (r • m) = (d.hom.app (op W) r) • rho N W m) ∧
        (∀ (N : FiniteCoefficientModules T A) (W W' : U.ProEt) (b : W' ⟶ W)
          (m : ((finiteCoefficientModulePullback j A).obj N).val.obj (op W)),
          rho N W' (((finiteCoefficientModulePullback j A).obj N).val.map b.op m) =
            N.val.map ((Scheme.proEtaleOpenComposition j).map b).op (rho N W m)) ∧
        (∀ (N N' : FiniteCoefficientModules T A) (h : N ⟶ N') (W : U.ProEt)
          (m : ((finiteCoefficientModulePullback j A).obj N).val.obj (op W)),
          rho N' W (((finiteCoefficientModulePullback j A).map h).val.app (op W) m) =
            h.val.app (op ((Scheme.proEtaleOpenComposition j).obj W)) (rho N W m)) ∧
        ∃ (_ : (SheafOfModules.pushforward.{u + 1} (F := Scheme.proEtaleBaseChange j)
            (J := Scheme.ProEt.topology T) (K := Scheme.ProEt.topology U)
            (finiteCoefficientDirectImageMap j A)).Additive)
          (adj : finiteCoefficientModulePullback j A ⊣ SheafOfModules.pushforward.{u + 1}
            (F := Scheme.proEtaleBaseChange j) (J := Scheme.ProEt.topology T)
            (K := Scheme.ProEt.topology U) (finiteCoefficientDirectImageMap j A)),
          (∀ (N : FiniteCoefficientModules T A) (V : T.ProEt) (m : N.val.obj (op V)),
            (adj.unit.app N).val.app (op V) m =
              (((SheafOfModules.pullbackPushforwardAdjunction.{u + 1}
                (finiteCoefficientModelRingUnit j A)).unit.app
                  ((Scheme.proEtaleModuleToModel (finiteCoefficientRingSheaf T A)).obj N)).val.app
                    (AsSmall.up.op.obj (op V))) m) ∧
          (∀ (N : FiniteCoefficientModules T A) (V : T.ProEt) (m : N.val.obj (op V)),
            rho N ((Scheme.proEtaleBaseChange j).obj V)
                ((adj.unit.app N).val.app (op V) m) =
              N.val.map (Scheme.proEtaleOpenSectionProjection j V).op m) := by
  let G := Scheme.proEtaleOpenComposition j
  let F := Scheme.proEtaleBaseChange j
  let : G.IsContinuous (Scheme.ProEt.topology U) (Scheme.ProEt.topology T) :=
    Scheme.ProEt.isContinuous_overMap (inferInstance : WeaklyEtale j)
  let : G.IsCocontinuous (Scheme.ProEt.topology U) (Scheme.ProEt.topology T) :=
    Scheme.ProEt.isCocontinuous_overMap (inferInstance : WeaklyEtale j)
  let P := finiteCoefficientPresheaf T A
  let c := (G.pushforwardContinuousSheafificationCompatibility RingCat.{u + 1}
    (Scheme.ProEt.topology U) (Scheme.ProEt.topology T)).app P
  let adj := MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ j
    (inferInstance : WeaklyEtale j) trivial
  have H₁ : Functor.whiskerRight (NatTrans.op adj.counit)
      (finiteCoefficientRingSheaf T A).obj =
      (finiteCoefficientDirectImageMap j A).hom ≫ F.op.whiskerLeft c.hom.hom := by
    apply sheafify_hom_ext (Scheme.ProEt.topology T) _ _
      (((Scheme.proEtaleSheafDirectImage j RingCat.{u + 1}).obj
        ((G.sheafPushforwardContinuous RingCat.{u + 1}
          (Scheme.ProEt.topology U) (Scheme.ProEt.topology T)).obj
          (finiteCoefficientRingSheaf T A))).property)
    have hc := G.toSheafify_pullbackSheafificationCompatibility RingCat.{u + 1}
      (Scheme.ProEt.topology U) (Scheme.ProEt.topology T) P
    apply NatTrans.ext
    funext V
    have hc' := congrArg (fun z ↦ z.app (F.op.obj V)) hc
    have hn := (toSheafify (Scheme.ProEt.topology T) P).naturality
      (adj.counit.app V.unop).op
    have hr' : toSheafify (Scheme.ProEt.topology T) P ≫
        (finiteCoefficientDirectImageMap j A).hom =
        finiteCoefficientDirectImagePresheafMap j A := by
      exact (sheafificationAdjunction (Scheme.ProEt.topology T) RingCat.{u + 1}).homEquiv
        _ _ |>.apply_symm_apply _
    change (toSheafify (Scheme.ProEt.topology T) P).app V ≫
        (finiteCoefficientRingSheaf T A).obj.map (adj.counit.app V.unop).op =
      ((toSheafify (Scheme.ProEt.topology T) P).app V ≫
        (finiteCoefficientDirectImageMap j A).hom.app V) ≫ c.hom.hom.app (F.op.obj V)
    rw [show (toSheafify (Scheme.ProEt.topology T) P).app V ≫
        (finiteCoefficientDirectImageMap j A).hom.app V =
        (finiteCoefficientDirectImagePresheafMap j A).app V from
      congrArg (fun z ↦ z.app V) hr']
    change _ = (finiteCoefficientDirectImageApp j A V) ≫ _
    dsimp only [finiteCoefficientDirectImageApp]
    change (toSheafify (Scheme.ProEt.topology U) (finiteCoefficientPresheaf U A)).app
        (F.op.obj V) ≫ c.hom.hom.app (F.op.obj V) =
        (toSheafify (Scheme.ProEt.topology T) P).app (G.op.obj (F.op.obj V)) at hc'
    rw [Category.assoc, hc']
    exact hn.symm
  have H₂ : c.hom.hom ≫ G.op.whiskerLeft (finiteCoefficientDirectImageMap j A).hom ≫
      Functor.whiskerRight (NatTrans.op adj.unit) (finiteCoefficientRingSheaf U A).obj =
        𝟙 (finiteCoefficientRingSheaf U A).obj := by
    apply NatTrans.ext
    funext V
    change c.hom.hom.app V ≫ (finiteCoefficientDirectImageMap j A).hom.app (G.op.obj V) ≫
      (finiteCoefficientRingSheaf U A).obj.map (adj.unit.app V.unop).op = 𝟙 _
    rw [← cancel_mono (c.hom.hom.app V)]
    simp only [Category.assoc]
    have hn := c.hom.hom.naturality (adj.unit.app V.unop).op
    change (finiteCoefficientRingSheaf U A).obj.map (adj.unit.app V.unop).op ≫
      c.hom.hom.app V = c.hom.hom.app (F.op.obj (G.op.obj V)) ≫
        (finiteCoefficientRingSheaf T A).obj.map (G.map (adj.unit.app V.unop)).op at hn
    rw [hn]
    have h := congrArg (fun z ↦ z.app (G.op.obj V)) H₁
    change (finiteCoefficientRingSheaf T A).obj.map
        (adj.counit.app (G.obj V.unop)).op =
      (finiteCoefficientDirectImageMap j A).hom.app (G.op.obj V) ≫
        c.hom.hom.app (F.op.obj (G.op.obj V)) at h
    rw [← Category.assoc ((finiteCoefficientDirectImageMap j A).hom.app _) _ _, ← h]
    simp only [Category.id_comp, ← Functor.map_comp, ← op_comp]
    have ht : G.map (adj.unit.app V.unop) ≫ adj.counit.app (G.obj V.unop) = 𝟙 _ :=
      adj.left_triangle_components V.unop
    rw [ht, op_id]
    exact (congrArg (fun z ↦ c.hom.hom.app V ≫ z)
      ((finiteCoefficientRingSheaf T A).obj.map_id _)).trans (Category.comp_id _)
  let R := SheafOfModules.pushforward.{u + 1} (F := G) c.hom
  let Q := SheafOfModules.pushforward.{u + 1} (F := F) (finiteCoefficientDirectImageMap j A)
  let a : R ⊣ Q := SheafOfModules.pushforwardPushforwardAdj adj c.hom
    (finiteCoefficientDirectImageMap j A) H₁ H₂
  let b := finiteModuleAdjunction j A
  let E := b.leftAdjointUniq a
  have hunit (N : FiniteCoefficientModules T A) (V : T.ProEt) (m : N.val.obj (op V)) :
      (b.unit.app N).val.app (op V) m =
        (((SheafOfModules.pullbackPushforwardAdjunction.{u + 1}
          (finiteCoefficientModelRingUnit j A)).unit.app
            ((Scheme.proEtaleModuleToModel (finiteCoefficientRingSheaf T A)).obj N)).val.app
              (AsSmall.up.op.obj (op V))) m := by
    obtain ⟨g, hg, ht⟩ := (finiteModuleAdjunction_existsUnique j A).choose_spec.1
      N ((finiteCoefficientModulePullback j A).obj N) (𝟙 _)
    have h := ht (op V) m
    rw [Adjunction.homEquiv_id, Adjunction.homEquiv_unit] at h
    change _ = g.val.app _
      ((((SheafOfModules.pullbackPushforwardAdjunction.{u + 1}
        (finiteCoefficientModelRingUnit j A)).unit.app
          ((Scheme.proEtaleModuleToModel (finiteCoefficientRingSheaf T A)).obj N)).val.app
            (AsSmall.up.op.obj (op V))) m) at h
    rw [hg] at h
    exact h
  let rho (N : FiniteCoefficientModules T A) (W : U.ProEt) :
      ((finiteCoefficientModulePullback j A).obj N).val.obj (op W) ≃+
        N.val.obj (op (G.obj W)) :=
    { toFun := (E.hom.app N).val.app (op W)
      invFun := (E.inv.app N).val.app (op W)
      left_inv := by
        intro m
        exact congrArg (fun h ↦ h.val.app (op W) m) (E.hom_inv_id_app N)
      right_inv := by
        intro m
        exact congrArg (fun h ↦ h.val.app (op W) m) (E.inv_hom_id_app N)
      map_add' := map_add ((E.hom.app N).val.app (op W)).hom }
  have hlinear (N : FiniteCoefficientModules T A) (W : U.ProEt)
      (r : (finiteCoefficientRingSheaf U A).obj.obj (op W))
      (m : ((finiteCoefficientModulePullback j A).obj N).val.obj (op W)) :
      rho N W (r • m) = (c.hom.hom.app (op W) r) • rho N W m := by
    exact map_smul ((E.hom.app N).val.app (op W)).hom r m
  have hsite (N : FiniteCoefficientModules T A) (W W' : U.ProEt) (z : W' ⟶ W)
      (m : ((finiteCoefficientModulePullback j A).obj N).val.obj (op W)) :
      rho N W' (((finiteCoefficientModulePullback j A).obj N).val.map z.op m) =
        N.val.map (G.map z).op (rho N W m) := by
    exact congrArg (fun h ↦ h.hom m) ((E.hom.app N).val.naturality z.op)
  have hmodule (N N' : FiniteCoefficientModules T A) (h : N ⟶ N') (W : U.ProEt)
      (m : ((finiteCoefficientModulePullback j A).obj N).val.obj (op W)) :
      rho N' W (((finiteCoefficientModulePullback j A).map h).val.app (op W) m) =
        h.val.app (op (G.obj W)) (rho N W m) := by
    exact congrArg (fun z ↦ z.val.app (op W) m) (E.hom.naturality h)
  have hr (N : FiniteCoefficientModules T A) (V : T.ProEt) (m : N.val.obj (op V)) :
      rho N (F.obj V) ((b.unit.app N).val.app (op V) m) =
        N.val.map (Scheme.proEtaleOpenSectionProjection j V).op m := by
    have h := b.unit_leftAdjointUniq_hom_app a N
    exact congrArg (fun z ↦ z.val.app (op V) m) h
  refine ⟨(sheafToPresheaf _ _).mapIso c, ?_, rho, hlinear, hsite, hmodule,
    finiteModulePushforward_additive j A, b, hunit, hr⟩
  intro W a
  have h := G.toSheafify_pullbackSheafificationCompatibility RingCat.{u + 1}
    (Scheme.ProEt.topology U) (Scheme.ProEt.topology T) P
  exact congrArg (fun z ↦ z.app (op W) ((finiteCoefficientConstants U A).app (op W) a)) h

end AlgebraicGeometry.ProEtale
