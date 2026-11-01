/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Tensor.FiniteTensorReductionData
import WeilConjectures.Algebra.Homology.Signed.SignedLineScalarTensorTower

/-! # Normalized semilinear maps between finite signed lines

Source: finite reduction of purity, proof Step 2, and coefficient-twist conventions.
(blueprint: lem-pur-finite-tensor-semilinear-reduction).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures.PurityFiniteSetting

open CategoryTheory.Limits Opposite
open SheafOfModules

private theorem firstLine_eq (P : PurityFiniteSetting.{u}) (T : Scheme.{u}) :
    P.finiteTensorFirstLine T =
      changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1} (P.finiteTensorIntegralMap T)
        (purTwistIntegralOne T P.coefficients.l P.extension) := by
  cases P with
  | mk F C E n hn =>
    cases n with
    | zero => exact False.elim (Nat.not_succ_le_zero 0 hn)
    | succ n => rfl

set_option allowUnsafeReducibility true in
attribute [local reducible] sheafCompose ModuleCat.restrictScalars
  ModuleCat.RestrictScalars.obj' SheafOfModules.unit PresheafOfModules.unit
  scalarTensorPower signedLinePower coefficientTwistLine finiteTensorLine
  finiteTensorLineSectionMap PresheafOfModules.restrictOver
  Functor.sheafPushforwardContinuous SheafOfModules.overFunctor
  SheafOfModules.pushforward PresheafOfModules.pushforward
  PresheafOfModules.pushforward₀ PresheafOfModules.pushforward₀Obj
  PresheafOfModules.restrictScalars PresheafOfModules.restrictScalarsObj Over.forget

attribute [local irreducible] changeOfRingsOfUniverses scalarExtensionSection
  scalarExtensionUnitIso siteSheafTensorTmul siteSheafTensorRight

private theorem integralMap_comp (P : PurityFiniteSetting.{u})
    (m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ P.level) (T : Scheme.{u}) :
    P.finiteTensorIntegralMap T ≫
      proEtaleConstantRingMap (T := T) (P.finiteReductionRingHom m hm hmn) =
    (P.finiteReductionSetting m hm).finiteTensorIntegralMap T := by
  unfold finiteTensorIntegralMap proEtaleConstantRingMap
  rw [← Functor.map_comp]
  congr 1

private theorem towerComparison (T : Scheme.{u})
    {R S V : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (α : R ⟶ S) (β : S ⟶ V) (γ : R ⟶ V) (h : α ≫ β = γ)
    (L : SheafOfModules.{u + 1}
      ((sheafCompose (ProEt.topology T) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)) :
    ∃ b : changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1} β
        (changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1} α L) ≅
        changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1} γ L,
      ∀ (U : T.ProEtᵒᵖ) (a : S.obj.obj U) (x : L.val.obj U),
        b.hom.val.app U (scalarExtensionSection.{u + 1, u, u + 1, u + 1} β _ U 1
          (scalarExtensionSection.{u + 1, u, u + 1, u + 1} α L U a x)) =
        scalarExtensionSection.{u + 1, u, u + 1, u + 1} γ L U (β.hom.app U a) x := by
  subst γ
  refine ⟨scalarExtensionTowerIso.{u + 1, u, u + 1, u + 1} α β L, ?_⟩
  intro U a x
  have hh := congrArg (fun f ↦ f.val.app U
    (scalarExtensionSection.{u + 1, u, u + 1, u + 1} β _ U 1
      (scalarExtensionSection.{u + 1, u, u + 1, u + 1} α L U a x)))
    (scalarExtensionTowerIso_hom.{u + 1, u, u + 1, u + 1} α β L)
  refine hh.trans ?_
  simpa only [one_mul] using
    scalarExtensionTowerForward_tmul.{u + 1, u, u + 1, u + 1} α β L U 1 a x

section

attribute [local irreducible] finiteTensorFirstLine

private theorem firstComparison (P : PurityFiniteSetting.{u})
    (m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ P.level) (T : Scheme.{u}) :
    ∃ b : changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1}
        (proEtaleConstantRingMap (T := T) (P.finiteReductionRingHom m hm hmn))
        (P.finiteTensorFirstLine T) ≅ (P.finiteReductionSetting m hm).finiteTensorFirstLine T,
      ∀ (U : T.ProEtᵒᵖ) (a : (proEtaleConstantRing T P.Ring).obj.obj U)
        (x : (purTwistIntegralOne T P.coefficients.l P.extension).val.obj U)
        (z : (P.finiteTensorFirstLine T).val.obj U),
        HEq z (scalarExtensionSection.{u + 1, u, u + 1, u + 1} (P.finiteTensorIntegralMap T)
          (purTwistIntegralOne T P.coefficients.l P.extension) U a x) →
        HEq (b.hom.val.app U (scalarExtensionSection.{u + 1, u, u + 1, u + 1}
          (proEtaleConstantRingMap (T := T) (P.finiteReductionRingHom m hm hmn))
          (P.finiteTensorFirstLine T) U 1 z))
          (scalarExtensionSection.{u + 1, u, u + 1, u + 1}
            ((P.finiteReductionSetting m hm).finiteTensorIntegralMap T)
            (purTwistIntegralOne T P.coefficients.l P.extension) U
            ((proEtaleConstantRingMap (T := T)
              (P.finiteReductionRingHom m hm hmn)).hom.app U a) x) := by
  generalize hL : P.finiteTensorFirstLine T = L
  generalize hK : (P.finiteReductionSetting m hm).finiteTensorFirstLine T = K
  have hL' := hL.symm.trans (firstLine_eq P T)
  have hK' := hK.symm.trans (firstLine_eq (P.finiteReductionSetting m hm) T)
  clear hL hK
  subst L
  subst K
  obtain ⟨b, hb⟩ := towerComparison T (P.finiteTensorIntegralMap T)
    (proEtaleConstantRingMap (T := T) (P.finiteReductionRingHom m hm hmn))
    ((P.finiteReductionSetting m hm).finiteTensorIntegralMap T)
    (integralMap_comp P m hm hmn T)
    (purTwistIntegralOne T P.coefficients.l P.extension)
  refine ⟨b, ?_⟩
  intro U a x z hz
  cases eq_of_heq hz
  exact heq_of_eq (hb U a x)

end

private theorem firstLine_locallyFree (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    [T.Over (Spec (.of P.field.k))] :
    ∃ (I : Type (u + 1)) (X : I → T.ProEt), (ProEt.topology T).CoversTop X ∧
      ∀ i, Nonempty ((P.finiteTensorFirstLine T).over (X i) ≅
        unit (((sheafCompose (ProEt.topology T) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
          (proEtaleConstantRing T P.Ring)).over (X i))) := by
  classical
  let : ∀ x : T, Invertible (P.coefficients.l : T.residueField x) := fun x ↦
    (show IsUnit (P.coefficients.l : T.residueField x) by
      simpa only [map_natCast] using
        (P.coefficientPrime_isUnit_stalk T (T ↘ Spec (.of P.field.k)) x).map
          (T.residue x).hom).invertible
  have hr : (P.finiteTensorFirstLine T).IsFiniteLocallyFreeOfRank 1 := by
    cases P with
    | mk F C E n hn =>
      cases n with
      | zero => exact False.elim (Nat.not_succ_le_zero 0 hn)
      | succ n =>
        change (purTwistFiniteOne T C.l E n).IsFiniteLocallyFreeOfRank 1
        infer_instance
  obtain ⟨I, X, hX, h⟩ :=
    (isFiniteLocallyFreeOfRank_iff_exists_over_iso_free
      (M := P.finiteTensorFirstLine T) (r := 1)).mp hr
  exact ⟨I, X, hX, fun i ↦ ⟨(h i).some ≪≫ freeUniqueIso (ULift.{u + 1} (Fin 1))⟩⟩

private theorem semilinearDual_ext (T : Scheme.{u})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (α : R ⟶ S)
    (H N : SheafOfModules.{u + 1}
      ((sheafCompose (ProEt.topology T) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R))
    (M : SheafOfModules.{u + 1}
      ((sheafCompose (ProEt.topology T) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S))
    (b : changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1} α N ≅ M)
    (f g : H ⟶ (restrictScalars.{u + 1}
      ((sheafCompose (ProEt.topology T) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map α)).obj
      (homObj.{u + 1, u, u + 1, u + 1} M (unit _)))
    (h : ∀ (U : T.ProEtᵒᵖ) (φ : H.val.obj U) (x : N.val.obj U),
      (f.val.app U φ).app (op (Over.mk (𝟙 U.unop)))
        (b.hom.val.app U (scalarExtensionSection.{u + 1, u, u + 1, u + 1} α N U 1 x)) =
      (g.val.app U φ).app (op (Over.mk (𝟙 U.unop)))
        (b.hom.val.app U (scalarExtensionSection.{u + 1, u, u + 1, u + 1} α N U 1 x))) : f = g := by
  let q : homObj.{u + 1, u, u + 1, u + 1} M (unit _) ≅ homObj.{u + 1, u, u + 1, u + 1}
        (changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1} α N) (unit _) :=
    { hom := homObjMap.{u + 1, u, u + 1, u + 1} b.hom (𝟙 _)
      inv := homObjMap.{u + 1, u, u + 1, u + 1} b.inv (𝟙 _)
      hom_inv_id := by
        simp only [homObjMap_comp_homObjMap, b.inv_hom_id, Category.id_comp]
        exact homObjMap_id.{u + 1, u, u + 1, u + 1}
      inv_hom_id := by
        simp only [homObjMap_comp_homObjMap, b.hom_inv_id, Category.id_comp]
        exact homObjMap_id.{u + 1, u, u + 1, u + 1} }
  have hl : scalarExtensionLift.{u + 1, u, u + 1, u + 1} α H _ f ≫ q.hom =
      scalarExtensionLift.{u + 1, u, u + 1, u + 1} α H _ g ≫ q.hom := by
    apply scalarExtensionDual_hom_ext α H N
    intro U s t φ x
    simp only [comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply,
      scalarExtensionLift_tmul]
    change (s • (show (homObj.{u + 1, u, u + 1, u + 1} M (unit _)).val.obj U from
        f.val.app U φ)).app (op (Over.mk (𝟙 U.unop)))
        (b.hom.val.app U (scalarExtensionSection.{u + 1, u, u + 1, u + 1} α N U t x)) =
      (s • (show (homObj.{u + 1, u, u + 1, u + 1} M (unit _)).val.obj U from
        g.val.app U φ)).app (op (Over.mk (𝟙 U.unop)))
        (b.hom.val.app U (scalarExtensionSection.{u + 1, u, u + 1, u + 1} α N U t x))
    have ht : b.hom.val.app U (scalarExtensionSection.{u + 1, u, u + 1, u + 1} α N U t x) =
        t • b.hom.val.app U (scalarExtensionSection.{u + 1, u, u + 1, u + 1} α N U 1 x) := by
      rw [← map_smul]
      congr 1
      simpa only [mul_one] using (scalarExtensionSection_smul α N U t 1 x).symm
    rw [ht]
    let φf : (homObj.{u + 1, u, u + 1, u + 1} M (unit _)).val.obj U := f.val.app U φ
    let φg : (homObj.{u + 1, u, u + 1, u + 1} M (unit _)).val.obj U := g.val.app U φ
    have hs (ψ : (homObj.{u + 1, u, u + 1, u + 1} M (unit _)).val.obj U)
        (z : M.val.obj U) :
        (s • ψ).app (op (Over.mk (𝟙 U.unop))) z =
          s • (show S.obj.obj U from ψ.app (op (Over.mk (𝟙 U.unop))) z) := by
      have hh := congrArg (fun k ↦ k.hom z)
        (PresheafOfModules.smul_app.{u + 1, u, u + 1, u + 1}
          (R := S.obj) (M := M.val)
          (N := (SheafOfModules.unit ((sheafCompose (ProEt.topology T)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S)).val)
          s ψ (op (Over.mk (𝟙 U.unop))))
      change (s • ψ).app (op (Over.mk (𝟙 U.unop))) z =
        S.obj.map (𝟙 U.unop).op s •
          (show S.obj.obj U from ψ.app (op (Over.mk (𝟙 U.unop))) z) at hh
      have hi := congrArg (fun k : S.obj.obj U ⟶ S.obj.obj U ↦ k s) (S.obj.map_id U)
      change S.obj.map (𝟙 U.unop).op s = s at hi
      exact hh.trans (congrArg (fun r : S.obj.obj U ↦
        r • (show S.obj.obj U from ψ.app (op (Over.mk (𝟙 U.unop))) z)) hi)
    rw [hs, hs]
    let y := b.hom.val.app U (scalarExtensionSection.{u + 1, u, u + 1, u + 1} α N U 1 x)
    have htf : φf.app (op (Over.mk (𝟙 U.unop))) (t • y) =
        t • (show S.obj.obj U from φf.app (op (Over.mk (𝟙 U.unop))) y) :=
      (show M.val.obj U →ₗ[S.obj.obj U] S.obj.obj U from
        (φf.app (op (Over.mk (𝟙 U.unop)))).hom).map_smul t y
    have htg : φg.app (op (Over.mk (𝟙 U.unop))) (t • y) =
        t • (show S.obj.obj U from φg.app (op (Over.mk (𝟙 U.unop))) y) :=
      (show M.val.obj U →ₗ[S.obj.obj U] S.obj.obj U from
        (φg.app (op (Over.mk (𝟙 U.unop)))).hom).map_smul t y
    change s • (show S.obj.obj U from φf.app (op (Over.mk (𝟙 U.unop))) (t • y)) =
      s • (show S.obj.obj U from φg.app (op (Over.mk (𝟙 U.unop))) (t • y))
    rw [htf, htg]
    exact congrArg (fun z : S.obj.obj U ↦ s • (t • z)) (h U φ x)
  have hl' : scalarExtensionLift.{u + 1, u, u + 1, u + 1} α H _ f =
      scalarExtensionLift.{u + 1, u, u + 1, u + 1} α H _ g := by
    have hh := congrArg (fun k ↦ k ≫ q.inv) hl
    simpa only [Category.assoc, q.hom_inv_id, Category.comp_id] using hh
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  have hh := congrArg (fun k ↦ k.val.app U
        (scalarExtensionSection.{u + 1, u, u + 1, u + 1} α H U 1 x)) hl'
  have hf := scalarExtensionLift_tmul.{u + 1, u, u + 1, u + 1} α H _ f U 1 x
  have hg := scalarExtensionLift_tmul.{u + 1, u, u + 1, u + 1} α H _ g U 1 x
  have hh' := hf.symm.trans (hh.trans hg)
  let φf : (homObj.{u + 1, u, u + 1, u + 1} M (unit _)).val.obj U := f.val.app U x
  let φg : (homObj.{u + 1, u, u + 1, u + 1} M (unit _)).val.obj U := g.val.app U x
  change (1 : S.obj.obj U) • φf = (1 : S.obj.obj U) • φg at hh'
  have hh'' : φf = φg := by simpa only [one_smul] using hh'
  exact hh''

private theorem scalarExtension_hom_ext_of_eq (T : Scheme.{u})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (α : R ⟶ S)
    (L : SheafOfModules.{u + 1}
      ((sheafCompose (ProEt.topology T) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R))
    (M : SheafOfModules.{u + 1}
      ((sheafCompose (ProEt.topology T) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S))
    (hM : M = changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1} α L)
    {H : SheafOfModules.{u + 1}
      ((sheafCompose (ProEt.topology T) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S)}
    (f g : M ⟶ H)
    (h : ∀ (U : T.ProEtᵒᵖ) (a : S.obj.obj U) (x : L.val.obj U) (z : M.val.obj U),
      HEq z
        (scalarExtensionSection.{u + 1, u, u + 1, u + 1} α L U a x) →
        f.val.app U z = g.val.app U z) :
    f = g := by
  subst M
  apply scalarExtension_hom_ext α L f g
  intro U a x
  exact h U a x _ HEq.rfl

/-- The ordinary signed-line reduction is uniquely determined before deriving it.
Source: thm-pur-finite-reduction-of-purity, proof Step 2 (invertible twists),
def-coefficient-twists-detailed; Stacks Tags 03EK and 03EM.
(blueprint: lem-pur-finite-tensor-semilinear-reduction).

Proof: at exponent zero take the coefficient quotient. At exponent one,
reassociate the integral-line scalar extension with the quotient from level n
to level m. The balanced map sends a tensor x to its tensor with the image of a.
This respects restriction and the scalar action, so sheafifies. Tensor this
map recursively on positive powers. The first line is locally free of rank one:
on a cover trivializing it, all these scalar extensions are the quotient unit.
Define the negative-power map by transporting the dual coefficient quotient
through this local basis. Evaluation determines that map independently of the
basis, so the local maps glue. The unit and degree-one balancing equations
fix the first two maps; local pure tensors generate the positive powers, giving
uniqueness inductively. For negative powers, the positive-power reduction
locally surjects onto the quotient unit, and evaluation against its local basis
fixes the dual map. Hence the entire family is unique. This also covers equal
levels and the empty scheme. -/
theorem existsUnique_finiteTensorSemilinearReduction (P : PurityFiniteSetting.{u})
    (m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ P.level) (T : Scheme.{u})
    [T.Over (Spec (.of P.field.k))] :
    ∃! c : P.FiniteTensorLineMaps m hm hmn T,
      P.FiniteTensorLineMapsNormalized m hm hmn T c := by
  let α := proEtaleConstantRingMap (T := T) (P.finiteReductionRingHom m hm hmn)
  let Q := P.finiteReductionSetting m hm
  obtain ⟨b, hb⟩ := firstComparison P m hm hmn T
  obtain ⟨B, hB, heval, _⟩ := exists_signedLineComparison.{u + 1, u, u + 1} α
    (P.finiteTensorFirstLine T) (Q.finiteTensorFirstLine T)
    (firstLine_locallyFree P T) (firstLine_locallyFree Q T) b
  let c : P.FiniteTensorLineMaps m hm hmn T := fun
    | .ofNat n => scalarExtensionEmbedding.{u + 1, u, u + 1, u + 1} α _ ≫
        (proEtaleCoefficientRestrictScalars T (P.finiteReductionRingHom m hm hmn)).map
          (B (.ofNat n)).hom
    | .negSucc n => scalarExtensionEmbedding.{u + 1, u, u + 1, u + 1} α _ ≫
        (proEtaleCoefficientRestrictScalars T (P.finiteReductionRingHom m hm hmn)).map
          (B (.negSucc n)).hom
  have hc : P.FiniteTensorLineMapsNormalized m hm hmn T c := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro U a
      change (B 0).hom.val.app U
        (scalarExtensionSection.{u + 1, u, u + 1, u + 1} α _ U 1 a) = α.hom.app U a
      have hh := congrArg (fun f ↦ f.val.app U
        (scalarExtensionSection.{u + 1, u, u + 1, u + 1} α _ U 1 a)) hB.1
      refine hh.trans ?_
      simpa only [one_mul] using scalarExtensionUnitIso_tmul α U 1 a
    · intro U a x z hz
      change HEq ((B 1).hom.val.app U (scalarExtensionSection.{u + 1, u, u + 1, u + 1} α _ U 1 z)) _
      rw [hB.2.1]
      exact hb U a x z hz
    · intro j U x y xB yB hx hy
      cases eq_of_heq hx
      cases eq_of_heq hy
      apply heq_of_eq
      change (B (.ofNat (j + 2))).hom.val.app U
        (scalarExtensionSection.{u + 1, u, u + 1, u + 1} α _ U 1
          (siteSheafTensorTmul.{u + 1, u, u + 1, u + 1}
            (A := proEtaleConstantRing T P.Ring)
            (P.finiteTensorLine T (.ofNat (j + 1))) (P.finiteTensorFirstLine T) U x y)) = _
      rw [hB.2.2.1 j U 1 x y, ← hB.2.1]
      rfl
    · intro j U φ x φB xB hφ hx
      cases eq_of_heq hφ
      cases eq_of_heq hx
      change ((B (.negSucc j)).hom.val.app U
        (scalarExtensionSection.{u + 1, u, u + 1, u + 1} α _ U 1 φ)).app
          (op (Over.mk (𝟙 U.unop)))
            ((B (.ofNat (j + 1))).hom.val.app U
              (scalarExtensionSection.{u + 1, u, u + 1, u + 1} α _ U 1 x)) =
        α.hom.app U (φ.app (op (Over.mk (𝟙 U.unop))) x)
      simpa only [mul_one] using heval j U 1 1 φ x
  refine ⟨c, hc, ?_⟩
  intro d hd
  have h1 : d 1 = c 1 := by
    apply scalarExtension_hom_ext_of_eq T (P.finiteTensorIntegralMap T)
      (purTwistIntegralOne T P.coefficients.l P.extension)
      (P.finiteTensorFirstLine T) (firstLine_eq P T)
    intro V a z w hw
    exact eq_of_heq ((hd.2.1 V a z w hw).trans (hc.2.1 V a z w hw).symm)
  have hpos : ∀ n : ℕ, d (.ofNat n) = c (.ofNat n) := by
    intro n
    induction n using Nat.twoStepInduction with
    | zero =>
      apply SheafOfModules.hom_ext
      apply PresheafOfModules.hom_ext
      intro U
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro a
      exact (hd.1 U a).trans (hc.1 U a).symm
    | one => exact h1
    | more n _ ih =>
      apply scalarTensor_hom_ext
        (P.finiteTensorLine T (.ofNat (n + 1))) (P.finiteTensorFirstLine T)
      intro U x y
      have hd' := hd.2.2.1 n U x y _ _ HEq.rfl HEq.rfl
      have hc' := hc.2.2.1 n U x y _ _ HEq.rfl HEq.rfl
      dsimp only [finiteTensorLineSectionMap] at hd' hc'
      rw [ih, h1] at hd'
      exact eq_of_heq (hd'.trans hc'.symm)
  funext r
  cases r with
  | ofNat n => exact hpos n
  | negSucc n =>
    apply semilinearDual_ext T α (P.finiteTensorLine T (.negSucc n))
      (P.finiteTensorLine T (.ofNat (n + 1)))
      (Q.finiteTensorLine T (.ofNat (n + 1))) (B (.ofNat (n + 1)))
    intro U φ x
    have hd' := hd.2.2.2 n U φ x _ _ HEq.rfl HEq.rfl
    have hc' := hc.2.2.2 n U φ x _ _ HEq.rfl HEq.rfl
    dsimp only [finiteTensorLineSectionMap] at hd' hc'
    rw [hpos (n + 1)] at hd'
    exact hd'.trans hc'.symm

end WeilConjectures.PurityFiniteSetting
