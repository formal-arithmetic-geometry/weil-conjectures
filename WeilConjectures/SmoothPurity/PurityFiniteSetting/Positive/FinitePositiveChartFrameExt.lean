/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.FiniteSignedTwistProducts

import WeilConjectures.Algebra.Homology.Signed.SignedLineScalarTensorTower
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModuleUnit
import WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicSectionCoordinates

/-! # Extensionality on compatible ordered frames

Source: finite-reduction proof Step 2, local rank-one gluing, expanded Step 8.
(blueprint: lem-pur-finite-positive-chart-frame-ext)
-/

@[expose] public section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures.PurityFiniteSetting

private theorem realization_naturality (T : Scheme.{u}) (A : Type u)
    [CommRing A] [Finite A]
    {M N : Sheaf (ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1, u} A))}
    (f : M ⟶ N) (V : T.ProEtᵒᵖ) (x : M.obj.obj V) :
    ((sfIntrinsicModuleEquivalence T A).functor.map f).val.app V
        (sfIntrinsicRealizationUnit T A M V x) =
      sfIntrinsicRealizationUnit T A N V (f.hom.app V x) := by
  exact (sfRealizationSectionEquiv_map A T f V x).symm

private theorem section_bijective (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    (r : ℤ) (V : T.ProEt) : Function.Bijective (P.finiteTensorSection T r V) := by
  let : Finite P.Ring := Padic.finite_coefficientExtensionRing
    P.coefficients.l P.extension P.level P.level_pos
  exact (sfIntrinsicSectionEquiv P.Ring T (P.finiteTensorLine T r)
    (Opposite.op V)).bijective

private theorem module_map_id {C : Type*} [Category C] {R : Cᵒᵖ ⥤ RingCat.{u + 1}}
    (M : PresheafOfModules.{u + 1} R) (V : Cᵒᵖ) (x : M.obj V) :
    M.map (𝟙 V) x = x := by
  rw [M.map_id]
  rfl

set_option maxHeartbeats 2000000 in
-- Constructing signed frames unfolds the intrinsic realization and slice module structures.
/-- Maps from one positive line are determined by compatible ordered frame vectors.
The target is an arbitrary coefficient sheaf; neither map is required to be invertible.
Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-lem-sp-reduction/
thm-pur-finite-reduction-of-purity.proof.md, Step 2, local invertible twists and
Step 3, rank-one gluing; expanded Step 8 of the root-chart construction.
(blueprint: lem-pur-finite-positive-chart-frame-ext).
Proof: the inverse first chart takes coefficient one to a generator of the first
line. On a trivializing pro-etale cover extend this generator to the coherent
signed frame: take coefficient one at zero, ordered tensor powers in positive
degrees, and the evaluation-dual bases in negative degrees. The scalar realization
unit and its counit identify the ordinary and intrinsic section modules, so these
frames have ordinary representatives satisfying the two heterogeneous equalities.
The assumed equality therefore gives equality of the two maps on the degree-d
basis generator. Both maps are linear over the constant coefficient sheaf, hence
agree on every local section, since every section is a multiple of the basis.
Their values on an arbitrary section agree after restriction to this cover; the
target sheaf's separatedness gives equality before restriction. Sheaf morphism
extensionality proves the claim. At degree zero the same argument uses the unit
basis, and on the empty scheme separatedness gives the unique map. -/
theorem finiteTensorPositiveChart_frame_ext (P : PurityFiniteSetting.{u})
    (T : Scheme.{u}) [T.Over (Spec (.of P.field.k))]
    (e₁ : P.finiteTensorFixedSheaf T 1 ≅
      𝟙_ (Sheaf (ProEt.topology T) (ModuleCat.{u + 1} P.Coefficient)))
    (d : ℕ) (M : Sheaf (ProEt.topology T) (ModuleCat.{u + 1} P.Coefficient))
    (f g : P.finiteTensorFixedSheaf T d ⟶ M)
    (h : ∀ (V : T.ProEt) (b : P.FiniteTensorFrame T V)
      (x₁ : (P.finiteTensorFixedSheaf T 1).obj.obj (Opposite.op V))
      (x : (P.finiteTensorFixedSheaf T d).obj.obj (Opposite.op V)),
      HEq (P.finiteTensorSection T 1 V x₁) (P.finiteTensorFrameBasis T V b 1) →
      e₁.hom.hom.app (Opposite.op V) x₁ =
        (Functor.LaxMonoidal.ε (sheafToPresheaf (ProEt.topology T)
          (ModuleCat.{u + 1} P.Coefficient))).app (Opposite.op V) (1 : P.Coefficient) →
      HEq (P.finiteTensorSection T d V x) (P.finiteTensorFrameBasis T V b d) →
      f.hom.app (Opposite.op V) x = g.hom.app (Opposite.op V) x) : f = g := by
  classical
  let : Finite P.Ring := Padic.finite_coefficientExtensionRing
    P.coefficients.l P.extension P.level P.level_pos
  let E := sfIntrinsicModuleEquivalence T P.Ring
  let q : P.finiteTensorFirstLine T ≅ proEtaleConstantModule T P.Ring :=
    (E.counitIso.app (P.finiteTensorLine T 1)).symm ≪≫ E.functor.mapIso e₁ ≪≫
      proEtaleConstantModuleUnit T P.Ring
  let x₁ (V : T.ProEtᵒᵖ) : (P.finiteTensorFixedSheaf T 1).obj.obj V :=
    e₁.inv.hom.app V
      ((Functor.LaxMonoidal.ε (sheafToPresheaf (ProEt.topology T)
        (ModuleCat.{u + 1} P.Coefficient))).app V (1 : P.Coefficient))
  have hx₁ (V : T.ProEtᵒᵖ) : e₁.hom.hom.app V (x₁ V) =
      (Functor.LaxMonoidal.ε (sheafToPresheaf (ProEt.topology T)
        (ModuleCat.{u + 1} P.Coefficient))).app V (1 : P.Coefficient) := by
    change ((e₁.inv ≫ e₁.hom).hom.app V) _ = _
    rw [e₁.inv_hom_id]
    rfl
  have hq (V : T.ProEtᵒᵖ) : q.hom.val.app V
      (P.finiteTensorSection T 1 V.unop (x₁ V)) =
        (1 : (proEtaleConstantRing T P.Ring).obj.obj V) := by
    let z := sfIntrinsicRealizationUnit T P.Ring (P.finiteTensorFixedSheaf T 1) V (x₁ V)
    have hc : (E.counitIso.app (P.finiteTensorLine T 1)).inv.val.app V
        ((E.counitIso.app (P.finiteTensorLine T 1)).hom.val.app V z) = z :=
      ConcreteCategory.congr_hom
        (congrArg (fun k ↦ k.val.app V)
          (E.counitIso.app (P.finiteTensorLine T 1)).hom_inv_id) z
    change (proEtaleConstantModuleUnit T P.Ring).hom.val.app V
      ((E.functor.map e₁.hom).val.app V
        ((E.counitIso.app (P.finiteTensorLine T 1)).inv.val.app V
          ((E.counitIso.app (P.finiteTensorLine T 1)).hom.val.app V z))) = _
    rw [hc, realization_naturality T P.Ring e₁.hom V (x₁ V)]
    change (proEtaleConstantModuleUnit T P.Ring).hom.val.app V
      (sfIntrinsicRealizationUnit T P.Ring (proEtaleFixedConstantModule T P.Ring) V
        (e₁.hom.hom.app V (x₁ V))) = _
    rw [hx₁]
    have hε : Functor.LaxMonoidal.ε (sheafToPresheaf (ProEt.topology T)
          (ModuleCat.{u + 1} P.Coefficient)) =
        toSheafify (ProEt.topology T) ((Functor.const T.ProEtᵒᵖ).obj
          (ModuleCat.of P.Coefficient P.Coefficient)) := by
      change (sheafificationAdjunction (ProEt.topology T)
        (ModuleCat.{u + 1} P.Coefficient)).homEquiv _ _ (𝟙 _) = _
      rw [Adjunction.homEquiv_unit]
      change toSheafify (ProEt.topology T) _ ≫ 𝟙 _ = _
      exact Category.comp_id _
    rw [hε]
    have hn := (proEtaleConstantModuleUnit_existsUnique T P.Ring).exists.choose_spec
      V (1 : P.Coefficient)
    dsimp only [proEtaleConstantModuleUnit, Coefficient, coefficientCommRing] at hn ⊢
    simp only [map_one] at hn
    convert hn using 1
    rfl
  have frame (V : T.ProEt) : ∃ b : P.FiniteTensorFrame T V,
      P.finiteTensorSection T 1 V (x₁ (Opposite.op V)) = b.basis 1 0 := by
    let e : (P.finiteTensorFirstLine T).val.obj (Opposite.op V) :=
      P.finiteTensorSection T 1 V (x₁ (Opposite.op V))
    have he (W : (Over V)ᵒᵖ) : Function.Bijective
        (fun r : (proEtaleConstantRing T P.Ring).obj.obj (Opposite.op W.unop.left) ↦
          r • (P.finiteTensorFirstLine T).val.map W.unop.hom.op e) := by
      let Q := ((SheafOfModules.evaluation _ (Opposite.op W.unop.left)).mapIso q).toLinearEquiv
      have hgen : Q ((P.finiteTensorFirstLine T).val.map W.unop.hom.op e) =
          (1 : (proEtaleConstantRing T P.Ring).obj.obj (Opposite.op W.unop.left)) := by
        have hn := PresheafOfModules.naturality_apply q.hom.val W.unop.hom.op e
        change q.hom.val.app _ _ =
          (proEtaleConstantRing T P.Ring).obj.map W.unop.hom.op
            (q.hom.val.app (Opposite.op V) e) at hn
        change q.hom.val.app _ _ = _
        rw [hn, hq, map_one]
      have hh (r : (proEtaleConstantRing T P.Ring).obj.obj (Opposite.op W.unop.left)) :
          Q (r • (P.finiteTensorFirstLine T).val.map W.unop.hom.op e) = r := by
        rw [Q.map_smul, hgen, smul_eq_mul, mul_one]
      constructor
      · intro r t hrt
        exact (hh r).symm.trans ((congrArg Q hrt).trans (hh t))
      · intro z
        exact ⟨Q z, Q.injective (hh _)⟩
    obtain ⟨v, ⟨hv, hv1⟩, _⟩ := SheafOfModules.existsUnique_signedLineBasisPowers.{u + 1, u, u + 1}
      (P.finiteTensorFirstLine T) (Opposite.op V) e he
    have hb (m : ℤ) : Function.Bijective
        (fun r : (proEtaleConstantRing T P.Ring).obj.obj (Opposite.op V) ↦ r • v m) := by
      have hh := hv.1 m (Opposite.op (Over.mk (𝟙 V)))
      simp only [Over.mk_hom] at hh
      erw [module_map_id] at hh
      exact hh
    let l (m : ℤ) := LinearEquiv.ofBijective
      ({ toFun := fun r ↦ r • v m
         map_add' := fun r t ↦ add_smul r t _
         map_smul' := fun r t ↦ mul_smul r t _ } :
        (proEtaleConstantRing T P.Ring).obj.obj (Opposite.op V) →ₗ[
          (proEtaleConstantRing T P.Ring).obj.obj (Opposite.op V)]
            (SheafOfModules.signedLinePower.{u + 1, u, u + 1} (P.finiteTensorFirstLine T) m).val.obj
              (Opposite.op V)) (hb m)
    let b (m : ℤ) := (Module.Basis.singleton (Fin 1)
      ((proEtaleConstantRing T P.Ring).obj.obj (Opposite.op V))).map (l m)
    have bval (m : ℤ) : b m 0 = v m := by
      change l m ((Module.Basis.singleton (Fin 1) _ ) 0) = v m
      rw [Module.Basis.singleton_apply]
      change (1 : (proEtaleConstantRing T P.Ring).obj.obj (Opposite.op V)) • v m = _
      exact one_smul _ _
    refine ⟨{ basis := b, zero := ?_, positive := ?_, negative := ?_ }, ?_⟩
    · exact (bval 0).trans hv.2.1
    · intro j
      erw [bval, bval, bval]
      exact hv.2.2.1 j
    · intro j
      erw [bval, bval]
      have hn := hv.2.2.2 j (Opposite.op (Over.mk (𝟙 V)))
      simp only [Over.mk_hom] at hn
      erw [module_map_id] at hn
      exact hn
    · change e = b 1 0
      rw [bval]
      exact hv1.symm
  apply E.functor.map_injective
  apply (cancel_epi (E.counitIso.app (P.finiteTensorLine T d)).inv).mp
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  obtain ⟨b, hb⟩ := frame V.unop
  apply ModuleCat.hom_ext
  apply (b.basis d).ext
  intro i
  have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
  subst i
  obtain ⟨x, hx⟩ := (section_bijective P T d V.unop).surjective (b.basis d 0)
  have hab := h V.unop b (x₁ V) x (heq_of_eq hb) (hx₁ V) (heq_of_eq hx)
  change (E.functor.map f).val.app V
      ((E.counitIso.app (P.finiteTensorLine T d)).inv.val.app V (b.basis d 0)) =
    (E.functor.map g).val.app V
      ((E.counitIso.app (P.finiteTensorLine T d)).inv.val.app V (b.basis d 0))
  rw [← hx]
  let z := sfIntrinsicRealizationUnit T P.Ring (P.finiteTensorFixedSheaf T d) V x
  have hc : (E.counitIso.app (P.finiteTensorLine T d)).inv.val.app V
      ((E.counitIso.app (P.finiteTensorLine T d)).hom.val.app V z) = z :=
    ConcreteCategory.congr_hom
      (congrArg (fun k ↦ k.val.app V)
        (E.counitIso.app (P.finiteTensorLine T d)).hom_inv_id) z
  change (E.functor.map f).val.app V
      ((E.counitIso.app (P.finiteTensorLine T d)).inv.val.app V
        ((E.counitIso.app (P.finiteTensorLine T d)).hom.val.app V z)) =
    (E.functor.map g).val.app V
      ((E.counitIso.app (P.finiteTensorLine T d)).inv.val.app V
        ((E.counitIso.app (P.finiteTensorLine T d)).hom.val.app V z))
  rw [hc]
  exact (realization_naturality T P.Ring f V x).trans
    ((congrArg (sfIntrinsicRealizationUnit T P.Ring M V) hab).trans
      (realization_naturality T P.Ring g V x).symm)

end WeilConjectures.PurityFiniteSetting
