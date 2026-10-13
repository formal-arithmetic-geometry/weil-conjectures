/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W3
-/
module

public import Sheaf.AlgebraicGeometry.PicardBaseChangeCounit

/-! # Tensor and unit coherence for a pairing on a pullback square

Source: Stacks Project, Tags 0095, 0096, 08HY and 0BDP.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry.Scheme.Modules

/-- Transport a pulled pairing across the square and the coefficient comparisons.
This is a monoidal coherence statement: a and b are arbitrary maps, g is an
arbitrary pairing satisfying the displayed pullback equation, and there is no
base-change map or adjunction unit in the conclusion.
Source: Stacks Project, Tags 0095 and 0096 (tensor pullback and composition),
Tag 0BDP, evaluation formula. (blueprint: lem-sc-picard-pairing-pullback-coherence)

Proof: Write P_k for tensor pullback, δ_k for picardTensorObjIso(k).hom,
u_k for picardTensorUnitIso(k).hom, C_A for the square comparison, and D_M
for the coefficient comparison. Put e_W = δ_qW.inv followed by P_qW(ev)
and u_qW, and define e_T similarly. Transport by picardTensorComparison
to ordinary pullback. Its composition comparison sends the iterated pure
tensor r tensor (s tensor m) to rs tensor m. This respects tensor products
and sends the unit generator to the unit generator; these formulas extend
to the sheafifications by the universal property. Hence composition and
square comparisons are compatible with both δ and u. Transport back.

Square tensor/unit coherence and naturality express the left side as
δ_pT followed by C_A tensor C_B, then δ_v.inv, then P_v of
(δ_pW.inv followed by P_pW(g) and u_pW), and finally u_v. Substitute hg:
δ_pW.inv cancels δ_pW, leaving P_v of (a tensor b followed by e_W).
Functoriality and tensor naturality move a tensor b through δ_v.inv.
The resulting expression is δ_pT followed by
(C_A followed by P_v(a)) tensor (C_B followed by P_v(b)),
then δ_v.inv, P_v(e_W), and u_v. Coefficient tensor/unit coherence gives
δ_v.inv followed by P_v(e_W) and u_v = (D_M tensor D_N) followed by e_T.
Substitute and use tensorHom_comp_tensorHom to combine the two tensor
morphisms. This is exactly the right side. No adjunction counit, base-change
map, inverse structure unit, finiteness or flatness is used. Zero pairings
and empty schemes obey the same functorial identities. -/
theorem picardPairing_pullback_coherence
    {X S W T : Scheme.{u}} (f : X ⟶ S) (j : W ⟶ S) (h : T ⟶ W)
    (M N : X.Modules) (ev : M ⊗ N ⟶ SheafOfModules.unit X.ringCatSheaf)
    (A B : W.Modules)
    (a : (tensorPullback (Limits.pullback.snd f j)).obj A ⟶
      (tensorPullback (Limits.pullback.fst f j)).obj M)
    (b : (tensorPullback (Limits.pullback.snd f j)).obj B ⟶
      (tensorPullback (Limits.pullback.fst f j)).obj N)
    (g : A ⊗ B ⟶ SheafOfModules.unit W.ringCatSheaf)
    (hg : (tensorPullback (Limits.pullback.snd f j)).map g ≫
        (picardTensorUnitIso (Limits.pullback.snd f j)).hom =
      (picardTensorObjIso (Limits.pullback.snd f j) A B).hom ≫ (a ⊗ₘ b) ≫
        (picardTensorObjIso (Limits.pullback.fst f j) M N).inv ≫
        (tensorPullback (Limits.pullback.fst f j)).map ev ≫
        (picardTensorUnitIso (Limits.pullback.fst f j)).hom) :
    (tensorPullback (Limits.pullback.snd f (h ≫ j))).map
      ((picardTensorObjIso h A B).inv ≫ (tensorPullback h).map g ≫
        (picardTensorUnitIso h).hom) ≫
      (picardTensorUnitIso (Limits.pullback.snd f (h ≫ j))).hom =
    (picardTensorObjIso (Limits.pullback.snd f (h ≫ j))
      ((tensorPullback h).obj A) ((tensorPullback h).obj B)).hom ≫
      (((picardBaseChangeSquareIso f j h A).hom ≫
          (tensorPullback (picardBaseChangeTop f j h)).map a ≫
          (picardBaseChangeCoefficientIso f j h M).hom) ⊗ₘ
        ((picardBaseChangeSquareIso f j h B).hom ≫
          (tensorPullback (picardBaseChangeTop f j h)).map b ≫
          (picardBaseChangeCoefficientIso f j h N).hom)) ≫
      (picardTensorObjIso (Limits.pullback.fst f (h ≫ j)) M N).inv ≫
      (tensorPullback (Limits.pullback.fst f (h ≫ j))).map ev ≫
      (picardTensorUnitIso (Limits.pullback.fst f (h ≫ j))).hom := by sorry

end AlgebraicGeometry.Scheme.Modules
