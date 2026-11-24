/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import WeilConjectures.AlgebraicGeometry.Coherent
public import WeilConjectures.AlgebraicGeometry.IdealModuleProductStalk
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.LinearAlgebra.Quotient.Basic
import WeilConjectures.AlgebraicGeometry.AffineCompatibleDenominatorData
import WeilConjectures.AlgebraicGeometry.IdealPowerNumeratorPresentation
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.Algebra.GroupWithZero.Action.Units
public import Mathlib.AlgebraicGeometry.AffineScheme

/-! # Affine denominator maps before annihilator quotient descent

## References

* Stacks Project, Tags 01PM and 01PQ
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false in
private theorem annihilates_on_affine_subopens
    {X : Scheme.{u}} {P : X.Modules}
    (j : P ⟶ SheafOfModules.unit X.ringCatSheaf) [P.IsQuasicoherent]
    (F : X.Modules) (V : X.affineOpens) (m : Γ(F, V.1))
    (hm : ∀ b : Γ(P, V.1), (show Γ(X, V.1) from j.app V.1 b) • m = 0)
    (W : X.Opens) (hWV : W ≤ V.1) (b : Γ(P, W)) :
    (show Γ(X, W) from j.app W b) • F.presheaf.map (homOfLE hWV).op m = 0 := by
  classical
  choose f hf hx using fun y : W ↦ V.2.exists_basicOpen_le y (hWV y.2)
  let B (y : W) := X.basicOpen (f y)
  refine TopCat.Sheaf.eq_of_locally_eq' ⟨F.presheaf, F.isSheaf⟩ B W
    (fun y ↦ homOfLE (hf y)) ?_ _ 0 ?_
  · intro y hy
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨y, hy⟩, hx ⟨y, hy⟩⟩
  · intro y
    rw [map_zero, F.map_smul]
    obtain ⟨e, c, hc⟩ := Modules.exists_map_eq_pow_smul_of_isAffineOpen P V.2 (f y)
      (P.presheaf.map (homOfLE (hf y)).op b)
    have hkill := congrArg
      (F.presheaf.map (homOfLE (X.basicOpen_le (f y))).op) (hm c)
    rw [map_zero, F.map_smul] at hkill
    have hj := (ConcreteCategory.congr_hom
      (j.mapPresheaf.naturality (homOfLE (X.basicOpen_le (f y))).op) c).symm
    change X.presheaf.map (homOfLE (X.basicOpen_le (f y))).op (j.app V.1 c) =
      j.app (B y) (P.presheaf.map (homOfLE (X.basicOpen_le (f y))).op c) at hj
    rw [hj, hc, Modules.Hom.app_smul] at hkill
    change (X.presheaf.map (homOfLE (X.basicOpen_le (f y))).op (f y) ^ e *
      (show Γ(X, B y) from j.app (B y)
        (P.presheaf.map (homOfLE (hf y)).op b))) •
        F.presheaf.map (homOfLE (X.basicOpen_le (f y))).op m = 0 at hkill
    rw [mul_smul] at hkill
    have hu : IsUnit (X.presheaf.map
        (homOfLE (X.basicOpen_le (f y))).op (f y) ^ e) :=
      (X.toRingedSpace.isUnit_res_basicOpen (f y)).pow e
    have hz := hu.smul_eq_zero.mp hkill
    have hn := (ConcreteCategory.congr_hom
      (j.mapPresheaf.naturality (homOfLE (hf y)).op) b).symm
    change X.presheaf.map (homOfLE (hf y)).op (j.app W b) =
      j.app (B y) (P.presheaf.map (homOfLE (hf y)).op b) at hn
    rw [hn]
    have heq : F.presheaf.map (homOfLE (hf y)).op
        (F.presheaf.map (homOfLE hWV).op m) =
          F.presheaf.map (homOfLE (X.basicOpen_le (f y))).op m := by
      rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
      rfl
    rw [heq]
    exact hz

set_option backward.isDefEq.respectTransparency false in
/-- The denominator construction gives an affine linear map modulo a submodule
of the specified annihilator, with the multiplication formula on affine sections.
(Stacks, Tags 01PM and 01PQ) -/
theorem ideal_power_affine_denominator_map
    {X : Scheme.{u}} {I : X.Modules}
    (ι : I ⟶ SheafOfModules.unit X.ringCatSheaf) [Mono ι]
    [I.IsQuasicoherent] [I.IsFiniteType]
    (F : X.Modules) [F.IsQuasicoherent]
    (U : X.Opens)
    (hU : ∀ x : X, x ∈ U ↔ Function.Surjective
      ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).map ι).hom)
    (A : ℕ → X.Modules) (a : ∀ n : ℕ, A n ⟶ F)
    (hmono : ∀ n : ℕ, Mono (a n))
    (hqc : ∀ n : ℕ, (A n).IsQuasicoherent)
    (hann : ∀ (n : ℕ) (W : X.Opens) (s : Γ(F, W)),
      s ∈ Set.range ((a n).app W) ↔
        ∀ (W' : X.Opens) (h : W' ≤ W)
          (b : Γ((idealSheafPower ι n).1, W')),
          (F.smul (U := W') ((idealSheafPower ι n).2.val.app (op W') b)).asHom.hom
            (F.presheaf.map (homOfLE h).op s) = 0)
    (hquot : ∀ (n : ℕ) (W : X.Opens), W ≤ U →
      Function.Bijective ((cokernel.π (a n)).app W))
    (V : X.affineOpens) (s : Γ(F, U)) :
    ∃ (n : ℕ) (K : Submodule Γ(X, V.1) Γ(F, V.1)),
      ((idealSheafPower ι n).1).IsQuasicoherent ∧
      K ≤ LinearMap.range ((a n).val.app (op V.1)).hom ∧
      ∃ f : Γ((idealSheafPower ι n).1, V.1) →ₗ[Γ(X, V.1)] (Γ(F, V.1) ⧸ K),
        ∀ (W : X.Opens) (hWU : W ≤ U) (hWV : W ≤ V.1)
          (b : Γ((idealSheafPower ι n).1, V.1)) (x : Γ(F, V.1)),
          f b = K.mkQ x →
          (cokernel.π (a n)).app W (F.presheaf.map (homOfLE hWV).op x) =
            ((cokernel (a n)).smul (U := W) ((idealSheafPower ι n).2.val.app (op W)
              (((idealSheafPower ι n).1).presheaf.map (homOfLE hWV).op b))).asHom.hom
              ((cokernel.π (a n)).app W (F.presheaf.map (homOfLE hWU).op s)) := by
  classical
  have _ := hmono
  have _ := hqc
  have _ := hquot
  obtain ⟨t, k, g, y, hk, hg, hcover, hcross, hfrac⟩ :=
    affine_compatible_denominator_data ι F U hU V s
  let n := t * k + 1
  obtain ⟨hP, hrange, E, p, q, hp, hq⟩ :=
    ideal_power_numerator_presentation ι F V t k g y hg hcross
  let : ((idealSheafPower ι n).1).IsQuasicoherent := hP
  let j := (idealSheafPower ι n).2
  let K : Submodule Γ(X, V.1) Γ(F, V.1) :=
    ⨅ i : Fin t, LinearMap.ker ((g i ^ k) •
      (LinearMap.id : Γ(F, V.1) →ₗ[Γ(X, V.1)] Γ(F, V.1)))
  have memK (m : Γ(F, V.1)) : m ∈ K ↔ ∀ i, g i ^ k • m = 0 := by
    simp [K]
  have hK : K ≤ LinearMap.range ((a n).val.app (op V.1)).hom := by
    intro m hm
    apply (hann n V.1 m).mpr
    apply annihilates_on_affine_subopens j F V m
    intro b
    let L : Ideal Γ(X, V.1) :=
      LinearMap.ker (LinearMap.toSpanSingleton Γ(X, V.1) Γ(F, V.1) m)
    have hL : Ideal.span (Set.range (fun i ↦ g i ^ k)) ≤ L := by
      apply Ideal.span_le.mpr
      rintro _ ⟨i, rfl⟩
      exact (memK m).mp hm i
    exact hL (hrange ⟨b, rfl⟩)
  have hker : LinearMap.ker p ≤ LinearMap.ker (K.mkQ.comp q) := by
    intro z hz
    apply (Submodule.Quotient.mk_eq_zero K).mpr
    apply (memK (q z)).mpr
    intro i
    rw [hq, show p z = 0 from hz, map_zero, zero_smul]
  let e := p.quotKerEquivOfSurjective hp
  let f := ((LinearMap.ker p).liftQ (K.mkQ.comp q) hker).comp e.symm.toLinearMap
  have hfp (z : E) : f (p z) = K.mkQ (q z) := by
    simp [f, e, LinearMap.quotKerEquivOfSurjective_symm_apply]
  refine ⟨n, K, hP, hK, f, ?_⟩
  intro W hWU hWV b x hfx
  obtain ⟨z, rfl⟩ := hp b
  have heq : K.mkQ (q z) = K.mkQ x := (hfp z).symm.trans hfx
  have hdiff : q z - x ∈ K := (Submodule.Quotient.eq K).mp heq
  have hscalar (i : Fin t) : g i ^ k • x =
      (show Γ(X, V.1) from j.app V.1 (p z)) • y i := by
    have hh := (memK (q z - x)).mp hdiff i
    rw [smul_sub, sub_eq_zero] at hh
    exact hh.symm.trans (hq i z)
  have hx : F.presheaf.map (homOfLE hWV).op x =
      (show Γ(X, W) from j.app W
        (((idealSheafPower ι n).1).presheaf.map (homOfLE hWV).op (p z))) •
          F.presheaf.map (homOfLE hWU).op s := by
    let B (i : Fin t) := W ⊓ X.basicOpen (g i)
    refine TopCat.Sheaf.eq_of_locally_eq' ⟨F.presheaf, F.isSheaf⟩ B W
      (fun i ↦ homOfLE inf_le_left) ?_ _ _ ?_
    · intro w hw
      have hwUV : w ∈ U ⊓ V.1 := ⟨hWU hw, hWV hw⟩
      rw [hcover] at hwUV
      obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hwUV
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, hw, hi⟩
    · intro i
      let hBV : B i ≤ V.1 := inf_le_left.trans hWV
      let hBU : B i ≤ U := inf_le_left.trans hWU
      have hi := hfrac i (B i) hBU hBV inf_le_right
      have hh := congrArg (F.presheaf.map (homOfLE hBV).op) (hscalar i)
      rw [F.map_smul, F.map_smul, ← hi] at hh
      have hj := (ConcreteCategory.congr_hom
        (j.mapPresheaf.naturality (homOfLE hBV).op) (p z)).symm
      change X.presheaf.map (homOfLE hBV).op (j.app V.1 (p z)) =
        j.app (B i) (((idealSheafPower ι n).1).presheaf.map
          (homOfLE hBV).op (p z)) at hj
      rw [hj, smul_comm] at hh
      have hu : IsUnit (X.presheaf.map (homOfLE hBV).op (g i ^ k)) := by
        have hu0 : IsUnit (X.presheaf.map
            (homOfLE (X.basicOpen_le (g i))).op (g i ^ k)) := by
          rw [map_pow]
          exact (X.toRingedSpace.isUnit_res_basicOpen (g i)).pow k
        have hu' := hu0.map (X.presheaf.map
          (homOfLE (show B i ≤ X.basicOpen (g i) from inf_le_right)).op).hom
        change IsUnit (X.presheaf.map (homOfLE inf_le_right : B i ⟶
          X.basicOpen (g i)).op (X.presheaf.map
            (homOfLE (X.basicOpen_le (g i))).op (g i ^ k))) at hu'
        rw [← ConcreteCategory.comp_apply, ← Functor.map_comp] at hu'
        exact hu' 
      have hh' := hu.smul_left_cancel.mp hh
      rw [F.map_smul]
      have hjW := (ConcreteCategory.congr_hom
        (j.mapPresheaf.naturality (homOfLE
          (show B i ≤ W from inf_le_left)).op)
            (((idealSheafPower ι n).1).presheaf.map (homOfLE hWV).op (p z))).symm
      change X.presheaf.map (homOfLE inf_le_left : B i ⟶ W).op
          (j.app W (((idealSheafPower ι n).1).presheaf.map (homOfLE hWV).op (p z))) =
        j.app (B i) (((idealSheafPower ι n).1).presheaf.map
          (homOfLE inf_le_left : B i ⟶ W).op
            (((idealSheafPower ι n).1).presheaf.map (homOfLE hWV).op (p z))) at hjW
      rw [hjW]
      convert hh' using 1 <;>
        simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp] <;> rfl
  change (cokernel.π (a n)).app W (F.presheaf.map (homOfLE hWV).op x) =
    (show Γ(X, W) from j.app W
      (((idealSheafPower ι n).1).presheaf.map (homOfLE hWV).op (p z))) •
        (cokernel.π (a n)).app W (F.presheaf.map (homOfLE hWU).op s)
  rw [hx, Modules.Hom.app_smul]

end AlgebraicGeometry.Scheme
