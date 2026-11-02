/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Positive.FinitePositiveRootCharts
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Tensor.FiniteTensorProductFrameExt

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures.PurityFiniteSetting

private theorem coordinate_identity {A M : Type*} [CommRing A] [AddCommGroup M]
    [Module A M] (q : M ≃ₗ[A] A) (f : M →ₗ[A] A) (x z : M)
    (hx : f x = 1) : f z • x = z := by
  have hq (y : M) : y = q y • q.symm 1 := by
    apply q.injective
    simp
  have hf (y : M) : f y = q y * f (q.symm 1) := by
    conv_lhs => rw [hq y]
    rw [map_smul, smul_eq_mul]
  have hunit : q x * f (q.symm 1) = 1 := (hf x).symm.trans hx
  apply q.injective
  rw [map_smul, smul_eq_mul, hf]
  calc
    (q z * f (q.symm 1)) * q x = q z * (q x * f (q.symm 1)) := by ring
    _ = q z := by rw [hunit, mul_one]

/-- A normalized line map sends a source frame generator to a reduced frame generator.
Source: finite reduction of purity, Step 2; Stacks 03EK and 03PK.
(blueprint: lem-pur-finite-tensor-first-sheaf-chart-reduction-unit-frame-frame)
Proof: let `z = c 1 (b.basis 1 0)` and `φ = c (-1) (b.basis (-1) 0)`. The negative
evaluation clause of `hc` (with `j = 0`) and `b.negative 0` give `φ z = 1`, and by
naturality on every restriction over `V`. In each rank-one chart of the reduced first
line, `f x = 1` implies `f y • x = y`; sheaf separatedness glues this, so every
restriction of `z` is a basis vector. The ordered signed-line basis powers of `z`
(`existsUnique_signedLineBasisPowers`) packaged by `frame_of_signed_basis` give a
reduced frame whose degree-one basis vector is `z`. -/
theorem finiteTensorFirstSheafChart_reduction_frame_exists
    (P : PurityFiniteSetting.{u}) (m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ P.level)
    (T : Scheme.{u}) [T.Over (Spec (.of P.field.k))]
    (c : P.FiniteTensorLineMaps m hm hmn T)
    (hc : P.FiniteTensorLineMapsNormalized m hm hmn T c)
    (V : T.ProEt) (b : P.FiniteTensorFrame T V) :
    ∃ bB : (P.finiteReductionSetting m hm).FiniteTensorFrame T V,
      P.finiteTensorLineSectionMap m hm hmn T c 1 (Opposite.op V)
          (P.finiteTensorFrameBasis T V b 1) =
        (P.finiteReductionSetting m hm).finiteTensorFrameBasis T V bB 1 := by
  classical
  let Q := P.finiteReductionSetting m hm
  let R := proEtaleConstantRing T Q.Ring
  let L := Q.finiteTensorFirstLine T
  let z : L.val.obj (Opposite.op V) :=
    P.finiteTensorLineSectionMap m hm hmn T c 1 (Opposite.op V)
      (P.finiteTensorFrameBasis T V b 1)
  let φ := P.finiteTensorLineSectionMap m hm hmn T c (Int.negSucc 0)
    (Opposite.op V) (b.basis (Int.negSucc 0) 0)
  have hφ : φ.app (Opposite.op (Over.mk (𝟙 V))) z =
      (1 : R.obj.obj (Opposite.op V)) := by
    have h := hc.2.2.2 0 (Opposite.op V) (b.basis (Int.negSucc 0) 0)
      (b.basis 1 0) φ z HEq.rfl HEq.rfl
    have hs' :
        ((b.basis (Int.negSucc 0) 0).app
          (Opposite.op (Over.mk (𝟙 V)))) (b.basis 1 0) =
          (1 : (proEtaleConstantRing T P.Ring).obj.obj (Opposite.op V)) :=
      b.negative 0
    change φ.app (Opposite.op (Over.mk (𝟙 V))) z = _ at h
    rw [hs', map_one] at h
    exact h
  obtain ⟨I, X, hX, h⟩ := first_line_charts Q T
  have heval (W : (Over V)ᵒᵖ) :
      φ.app W (L.val.map W.unop.hom.op z) =
        (1 : R.obj.obj (Opposite.op W.unop.left)) := by
    have hn := PresheafOfModules.naturality_apply φ
      (Over.homMk W.unop.hom (Category.comp_id _) :
        W.unop ⟶ Over.mk (𝟙 V)).op z
    change φ.app W (L.val.map W.unop.hom.op z) =
      R.obj.map W.unop.hom.op (φ.app (Opposite.op (Over.mk (𝟙 V))) z) at hn
    rw [hφ, map_one] at hn
    exact hn
  have he (W : (Over V)ᵒᵖ) : Function.Bijective
      (fun a : R.obj.obj (Opposite.op W.unop.left) ↦
        a • L.val.map W.unop.hom.op z) := by
    have hid (y : L.val.obj (Opposite.op W.unop.left)) :
        φ.app W y • L.val.map W.unop.hom.op z = y := by
      apply L.isSheaf.isSeparated _ _ (hX W.unop.left)
      intro Z k hk
      obtain ⟨i, ⟨g⟩⟩ := hk
      let WZ : (Over V)ᵒᵖ := Opposite.op (Over.mk (k ≫ W.unop.hom))
      let qi := (SheafOfModules.evaluation _ (Opposite.op (Over.mk g))).mapIso
        ((h i).some)
      let q : L.val.obj (Opposite.op Z) ≃ₗ[R.obj.obj (Opposite.op Z)]
          R.obj.obj (Opposite.op Z) := qi.toLinearEquiv
      have hh := coordinate_identity q (φ.app WZ).hom
        (L.val.map (k ≫ W.unop.hom).op z) (L.val.map k.op y) (heval WZ)
      have hn := PresheafOfModules.naturality_apply φ
        (Over.homMk k : Over.mk (k ≫ W.unop.hom) ⟶ W.unop).op y
      change φ.app WZ (L.val.map k.op y) = R.obj.map k.op (φ.app W y) at hn
      change L.val.map k.op (φ.app W y • L.val.map W.unop.hom.op z) =
        L.val.map k.op y
      rw [L.val.map_smul]
      change R.obj.map k.op (φ.app W y) •
        L.val.map k.op (L.val.map W.unop.hom.op z) = L.val.map k.op y
      rw [← hn, ← PresheafOfModules.map_comp_apply]
      exact hh
    constructor
    · intro a b hab
      have hf := congrArg (φ.app W) hab
      have ha := (φ.app W).hom.map_smul a (L.val.map W.unop.hom.op z)
      have hb := (φ.app W).hom.map_smul b (L.val.map W.unop.hom.op z)
      rw [ha, hb, heval, smul_eq_mul, smul_eq_mul, mul_one, mul_one] at hf
      exact hf
    · intro y
      exact ⟨φ.app W y, hid y⟩
  obtain ⟨E, ⟨hE, hE1⟩, _⟩ :=
    SheafOfModules.existsUnique_signedLineBasisPowers.{u + 1, u, u + 1} L
      (Opposite.op V) z he
  obtain ⟨bB, hbB⟩ := frame_of_signed_basis Q T V E hE
  refine ⟨bB, ?_⟩
  exact hE1.symm.trans (hbB 1).symm

end WeilConjectures.PurityFiniteSetting
