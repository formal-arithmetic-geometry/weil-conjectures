/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Reduction.FiniteReductionRootCharts

/-! # The power transition of the ordinary coefficient root line -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures.PurityFiniteSetting

private theorem rootSection_power (P : PurityFiniteSetting.{u})
    (T : Scheme.{u}) [T.Over (Spec (.of P.field.k))] (c : ℕ) (ζ ζ' : P.field.k)
    (hζ : IsPrimitiveRoot ζ P.diagonalExponent)
    (hζ' : IsPrimitiveRoot ζ' P.diagonalExponent) (hc : ζ = ζ' ^ c)
    (W : T.Etaleᵒᵖ) :
    P.finiteReductionRootSection T ζ hζ W =
      c • P.finiteReductionRootSection T ζ' hζ' W := by
  let N := P.diagonalExponent
  let f := T ↘ Spec (.of P.field.k)
  let ρ : P.field.k →+* Γ(T, ⊤) := ((Scheme.ΓSpecIso (.of P.field.k)).inv ≫ f.appTop).hom
  let u := (hζ.isUnit (NeZero.ne N)).map ρ
  let u' := (hζ'.isUnit (NeZero.ne N)).map ρ
  have hu : u.unit ^ N = 1 := Units.ext (by
    rw [Units.val_pow_eq_pow_val, IsUnit.unit_spec, ← map_pow, hζ.pow_eq_one, map_one]
    rfl)
  have hu' : u'.unit ^ N = 1 := Units.ext (by
    rw [Units.val_pow_eq_pow_val, IsUnit.unit_spec, ← map_pow, hζ'.pow_eq_one, map_one]
    rfl)
  apply T.injective_kernelι_app N W
  rw [map_nsmul]
  let Z := (Functor.const T.Etaleᵒᵖ).obj
    (AddCommGrpCat.of (ULift.{u + 1} (ZMod N)))
  have hnorm (v : Γ(T, ⊤)ˣ) (hv : v ^ N = 1) :
      (kernel.ι (N • 𝟙 T.gmSheaf)).hom.app W
        ((T.constantZModToRootsOfUnitySheaf N v hv).hom.app W
          ((toSheafify T.smallEtaleTopology Z).app W (ULift.up (1 : ZMod N)))) =
      (T.zmodToGmPresheaf N v hv).app W (ULift.up (1 : ZMod N)) := by
    have e : T.constantZModToRootsOfUnitySheaf N v hv ≫ kernel.ι (N • 𝟙 T.gmSheaf) =
        T.constantZModToGmSheaf N v hv := kernel.lift_ι _ _ _
    have e' : toSheafify T.smallEtaleTopology Z ≫
        (T.constantZModToRootsOfUnitySheaf N v hv ≫
          kernel.ι (N • 𝟙 T.gmSheaf)).hom = T.zmodToGmPresheaf N v hv := by
      rw [e]
      exact T.toSheafify_constantZModToGmSheaf N v hv
    exact congrArg (fun g ↦ g.app W (ULift.up (1 : ZMod N))) e'
  change (kernel.ι (N • 𝟙 T.gmSheaf)).hom.app W
      ((T.constantZModToRootsOfUnitySheaf N u.unit hu).hom.app W _) =
    c • (kernel.ι (N • 𝟙 T.gmSheaf)).hom.app W
      ((T.constantZModToRootsOfUnitySheaf N u'.unit hu').hom.app W _)
  rw [hnorm, hnorm]
  let q : T.gmPresheaf.obj W ≃+ Additive (Γ(W.unop.left, ⊤)ˣ) := AddEquiv.ulift
  apply q.injective
  rw [map_nsmul]
  apply Additive.toMul.injective
  apply Units.ext
  rw [toMul_nsmul, Units.val_pow_eq_pow_val]
  have hq (x : T.gmPresheaf.obj W) : q x = x.down := by rfl
  have e₁ : ((q ((T.zmodToGmPresheaf N u.unit hu).app W
      (ULift.up (1 : ZMod N)))).toMul : Γ(W.unop.left, ⊤)) =
      W.unop.hom.appTop (u.unit : Γ(T, ⊤)) := by
    rw [hq]
    simpa only [Nat.cast_one, pow_one] using
      T.zmodToGmPresheaf_app_natCast N u.unit hu W 1
  have e₂ : ((q ((T.zmodToGmPresheaf N u'.unit hu').app W
      (ULift.up (1 : ZMod N)))).toMul : Γ(W.unop.left, ⊤)) =
      W.unop.hom.appTop (u'.unit : Γ(T, ⊤)) := by
    rw [hq]
    simpa only [Nat.cast_one, pow_one] using
      T.zmodToGmPresheaf_app_natCast N u'.unit hu' W 1
  rw [e₁, e₂]
  change W.unop.hom.appTop (ρ ζ) = W.unop.hom.appTop (ρ ζ') ^ c
  rw [hc, map_pow, map_pow]

private theorem rootTrivialization_hom_power (P : PurityFiniteSetting.{u})
    (T : Scheme.{u}) [T.Over (Spec (.of P.field.k))] (c : ℕ) (ζ ζ' : P.field.k)
    (hζ : IsPrimitiveRoot ζ P.diagonalExponent)
    (hζ' : IsPrimitiveRoot ζ' P.diagonalExponent) (hc : ζ = ζ' ^ c) :
    (P.finiteReductionRootTrivialization T ζ hζ).hom =
      c • (P.finiteReductionRootTrivialization T ζ' hζ').hom := by
  apply Sheaf.hom_ext
  apply sheafify_hom_ext T.smallEtaleTopology _ _
    (Scheme.finiteEtaleTateLine T P.diagonalExponent P.Coefficient
      P.diagonalExponent_annihilates).property
  apply NatTrans.ext
  funext W
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  let Z := (Functor.const T.Etaleᵒᵖ).obj (ModuleCat.of P.Coefficient P.Coefficient)
  change (P.finiteReductionRootTrivialization T ζ hζ).hom.hom.app W
      ((toSheafify T.smallEtaleTopology Z).app W a) =
    c • (P.finiteReductionRootTrivialization T ζ' hζ').hom.hom.app W
      ((toSheafify T.smallEtaleTopology Z).app W a)
  have e₁ := (P.existsUnique_finiteReductionRootTrivialization T ζ hζ).choose_spec.1 W a
  have e₂ := (P.existsUnique_finiteReductionRootTrivialization T ζ' hζ').choose_spec.1 W a
  refine e₁.trans ?_
  refine Eq.trans ?_ (congrArg (fun x ↦ c • x) e₂.symm)
  rw [rootSection_power P T c ζ ζ' hζ hζ' hc W]
  unfold Scheme.finiteEtaleTateOneGenerator
  rw [TensorProduct.tmul_smul, map_nsmul]

/-- The inverse ordinary coefficient-root charts turn a field power relation into
natural-number scalar multiplication.

Source: Stacks 03PK, `a ↦ ζ ^ a`, and blueprint finite reduction of purity Step 2
(blueprint: lem-pur-finite-root-line-power-transition).

Proof: on the constant section `1` of the constant Z/N sheaf, the primitive-root
map has value ζ. Compose with the kernel inclusion of roots into Gm, which is
injective on sections. The sheafification unit equation and the formula for the
map into Gm identify the section for ζ = ζ' ^ c with c times the section for ζ',
since roots use the additive group of multiplicative units. The coefficient-line
chart is normalized by a ↦ a tensor ζ. Additivity of tensor and sheafification
therefore gives t_ζ.hom = c times t_ζ'.hom on every constant coefficient section.
Sheafification uniqueness proves the equality of homs. Compose with the two inverse
charts to get t_ζ'.inv = c times t_ζ.inv. This uses only ordinary sheaf maps, and
holds also on the empty scheme; it uses no derived tensor or arbitrary complex. -/
theorem finiteReductionRootTrivialization_inv_power (P : PurityFiniteSetting.{u})
    (T : Scheme.{u}) [T.Over (Spec (.of P.field.k))] (c : ℕ) (ζ ζ' : P.field.k)
    (hζ : IsPrimitiveRoot ζ P.diagonalExponent)
    (hζ' : IsPrimitiveRoot ζ' P.diagonalExponent) (hc : ζ = ζ' ^ c) :
    (P.finiteReductionRootTrivialization T ζ' hζ').inv =
      c • (P.finiteReductionRootTrivialization T ζ hζ).inv := by
  apply (cancel_epi (P.finiteReductionRootTrivialization T ζ' hζ').hom).mp
  rw [Preadditive.comp_nsmul, ← Preadditive.nsmul_comp,
    ← rootTrivialization_hom_power P T c ζ ζ' hζ hζ' hc,
    Iso.hom_inv_id, Iso.hom_inv_id]

end WeilConjectures.PurityFiniteSetting
