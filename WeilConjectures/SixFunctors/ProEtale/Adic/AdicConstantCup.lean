/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.IntegralAdicLimit
public import WeilConjectures.SixFunctors.ProEtale.Adic.FiniteAdicCup

/-!
# The cup product on `Hⁿ(S, ℤ_ℓ)` and `Hⁿ(S, ℚ̄_ℓ)`

Let `S` be quasi-compact and quasi-separated with finite cohomology groups `Hᵏ(S, ℤ/ℓᵐ)`. If the
finite-level cup products (`AlgebraicGeometry.ProEtale.finiteAdicCup`) are compatible with the
transition maps `Hⁿ(S, ℤ/ℓᵐ⁺¹) ⟶ Hⁿ(S, ℤ/ℓᵐ)`
(`AlgebraicGeometry.ProEtale.FiniteAdicCupCompatible`), they lift to a `ℤ_ℓ`-bilinear cup product
on `Hⁿ(S, ℤ_ℓ) = lim Hⁿ(S, ℤ/ℓᵐ)` (`AlgebraicGeometry.ProEtale.integralAdicCup`), whose base
change is a `ℚ̄_ℓ`-bilinear cup product on `Hⁿ(S, ℚ̄_ℓ) = ℚ̄_ℓ ⊗ Hⁿ(S, ℤ_ℓ)`
(`AlgebraicGeometry.ProEtale.adicConstantCup`). Both are graded commutative and, for an
automorphism `e` of a connected `S`, compatible with the pullbacks `e^*`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (l : ℕ) [Fact l.Prime] (S : Scheme.{u})

/-- The finite-level cup products are compatible with the transition maps
`Hⁿ(S, ℤ/ℓᵐ⁺¹) ⟶ Hⁿ(S, ℤ/ℓᵐ)`. -/
def FiniteAdicCupCompatible [CompactSpace S] [QuasiSeparatedSpace S] : Prop :=
  ∀ (m i j k : ℕ) (h : i + j = k) (a : FiniteAdicH S l (m + 1) i)
    (b : FiniteAdicH S l (m + 1) j),
    finiteAdicTransition S l m k (finiteAdicCup l (m + 1) S i j k h a b) =
      finiteAdicCup l m S i j k h (finiteAdicTransition S l m i a)
        (finiteAdicTransition S l m j b)

variable {l S} [CompactSpace S] [QuasiSeparatedSpace S]
  (hfin : ∀ m k, Finite (FiniteAdicH S l m k)) (hc : FiniteAdicCupCompatible l S)

/-- The cup product `Hⁱ(S, ℤ_ℓ) × Hʲ(S, ℤ_ℓ) ⟶ Hᵏ(S, ℤ_ℓ)`, `i + j = k`: the limit of the
finite-level cup products. -/
noncomputable def integralAdicCup (i j k : ℕ) (h : i + j = k) :
    IntegralAdicH S l i →ₗ[ℤ_[l]] IntegralAdicH S l j →ₗ[ℤ_[l]] IntegralAdicH S l k :=
  integralAdicBilinear (fun m k' _ ↦ hfin m k') (fun m ↦ finiteAdicCup l m S i j k h)
    (fun m a b ↦ hc m i j k h a b)

lemma reduction_integralAdicCup (i j k : ℕ) (h : i + j = k) (m : ℕ) (x : IntegralAdicH S l i)
    (y : IntegralAdicH S l j) :
    reduction S l m k (integralAdicCup hfin hc i j k h x y) =
      finiteAdicCup l m S i j k h (reduction S l m i x) (reduction S l m j y) :=
  reduction_integralAdicBilinear _ _ _ m x y

/-- The cup product on `Hⁿ(S, ℤ_ℓ)` is graded commutative. -/
theorem integralAdicCup_comm (i j k : ℕ) (h : i + j = k) (x : IntegralAdicH S l i)
    (y : IntegralAdicH S l j) :
    integralAdicCup hfin hc j i k (by omega) y x =
      (((i : ℤ) * j).negOnePow : ℤ) • integralAdicCup hfin hc i j k h x y :=
  eq_of_forall_reduction_eq (fun m k' _ ↦ hfin m k') _ _ fun m ↦ by
    rw [reduction_integralAdicCup, map_zsmul, reduction_integralAdicCup, finiteAdicCup_comm]

/-- The cup product on `Hⁿ(S, ℤ_ℓ)` is compatible with the pullback along an automorphism of a
connected `S`. -/
theorem integralAdicCup_pullback [ConnectedSpace S] (e : S ≅ S) (i j k : ℕ) (h : i + j = k)
    (x : IntegralAdicH S l i) (y : IntegralAdicH S l j) :
    integralAdicHPullback e l k (integralAdicCup hfin hc i j k h x y) =
      integralAdicCup hfin hc i j k h (integralAdicHPullback e l i x)
        (integralAdicHPullback e l j y) :=
  eq_of_forall_reduction_eq (fun m k' _ ↦ hfin m k') _ _ fun m ↦ by
    rw [reduction_integralAdicHPullback, reduction_integralAdicCup, reduction_integralAdicCup,
      reduction_integralAdicHPullback, reduction_integralAdicHPullback, finiteAdicCup_pullback]

section Rational

/-- The `ℚ̄_ℓ`-linear extension of `y ↦ x ⌣ y`, for an integral class `x`. -/
noncomputable def adicConstantCupAux (i j k : ℕ) (h : i + j = k) :
    letI : Module ℤ_[l] (AdicConstantH l S j →ₗ[PadicAlgCl l] AdicConstantH l S k) :=
      Module.compHom _ (algebraMap ℤ_[l] (PadicAlgCl l))
    IntegralAdicH S l i →ₗ[ℤ_[l]] (AdicConstantH l S j →ₗ[PadicAlgCl l] AdicConstantH l S k) :=
  letI : Module ℤ_[l] (AdicConstantH l S j →ₗ[PadicAlgCl l] AdicConstantH l S k) :=
    Module.compHom _ (algebraMap ℤ_[l] (PadicAlgCl l))
  { toFun x := (isBaseChange_integralToAdicConstantH l S j).lift
      ((integralToAdicConstantH l S k).comp (integralAdicCup hfin hc i j k h x))
    map_add' x x' := (isBaseChange_integralToAdicConstantH l S j).algHom_ext _ _ fun y ↦ by
      rw [LinearMap.add_apply, IsBaseChange.lift_eq, IsBaseChange.lift_eq, IsBaseChange.lift_eq]
      simp only [LinearMap.coe_comp, Function.comp_apply, map_add, LinearMap.add_apply]
    map_smul' r x := (isBaseChange_integralToAdicConstantH l S j).algHom_ext _ _ fun y ↦ by
      rw [RingHom.id_apply, IsBaseChange.lift_eq]
      change _ = algebraMap ℤ_[l] (PadicAlgCl l) r •
        (isBaseChange_integralToAdicConstantH l S j).lift
          ((integralToAdicConstantH l S k).comp (integralAdicCup hfin hc i j k h x))
          (integralToAdicConstantH l S j y)
      rw [IsBaseChange.lift_eq]
      simp only [LinearMap.coe_comp, Function.comp_apply, map_smul, LinearMap.smul_apply]
      exact (algebraMap_smul (PadicAlgCl l) r
        (integralToAdicConstantH l S k (integralAdicCup hfin hc i j k h x y))).symm }

/-- The cup product `Hⁱ(S, ℚ̄_ℓ) × Hʲ(S, ℚ̄_ℓ) ⟶ Hᵏ(S, ℚ̄_ℓ)`, `i + j = k`: the base change of
the cup product on `Hⁿ(S, ℤ_ℓ)`. -/
noncomputable def adicConstantCup (i j k : ℕ) (h : i + j = k) :
    AdicConstantH l S i →ₗ[PadicAlgCl l] AdicConstantH l S j →ₗ[PadicAlgCl l]
      AdicConstantH l S k :=
  letI : Module ℤ_[l] (AdicConstantH l S j →ₗ[PadicAlgCl l] AdicConstantH l S k) :=
    Module.compHom _ (algebraMap ℤ_[l] (PadicAlgCl l))
  haveI : IsScalarTower ℤ_[l] (PadicAlgCl l)
      (AdicConstantH l S j →ₗ[PadicAlgCl l] AdicConstantH l S k) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  (isBaseChange_integralToAdicConstantH l S i).lift (adicConstantCupAux hfin hc i j k h)

lemma adicConstantCup_integralToAdicConstantH (i j k : ℕ) (h : i + j = k)
    (x : IntegralAdicH S l i) (y : IntegralAdicH S l j) :
    adicConstantCup hfin hc i j k h (integralToAdicConstantH l S i x)
        (integralToAdicConstantH l S j y) =
      integralToAdicConstantH l S k (integralAdicCup hfin hc i j k h x y) := by
  let : Module ℤ_[l] (AdicConstantH l S j →ₗ[PadicAlgCl l] AdicConstantH l S k) :=
    Module.compHom _ (algebraMap ℤ_[l] (PadicAlgCl l))
  have : IsScalarTower ℤ_[l] (PadicAlgCl l)
      (AdicConstantH l S j →ₗ[PadicAlgCl l] AdicConstantH l S k) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  unfold adicConstantCup
  rw [IsBaseChange.lift_eq]
  exact IsBaseChange.lift_eq _ _ y

/-- **The cup product on `Hⁿ(S, ℚ̄_ℓ)` is graded commutative**: `y ⌣ x = (-1)^{ij} x ⌣ y`. -/
theorem adicConstantCup_comm (i j k : ℕ) (h : i + j = k) (x : AdicConstantH l S i)
    (y : AdicConstantH l S j) :
    adicConstantCup hfin hc j i k (by omega) y x =
      (((i : ℤ) * j).negOnePow : ℤ) • adicConstantCup hfin hc i j k h x y := by
  have := congrArg (fun φ ↦ φ x y) ((isBaseChange_integralToAdicConstantH l S i).algHom_ext
    (adicConstantCup hfin hc j i k (by omega)).flip
    ((((i : ℤ) * j).negOnePow : ℤ) • adicConstantCup hfin hc i j k h) fun a ↦
      (isBaseChange_integralToAdicConstantH l S j).algHom_ext _ _ fun b ↦ by
        simp only [LinearMap.flip_apply, LinearMap.smul_apply,
          adicConstantCup_integralToAdicConstantH]
        rw [integralAdicCup_comm hfin hc i j k h a b, map_zsmul])
  simpa using this

/-- **The cup product on `Hⁿ(S, ℚ̄_ℓ)` is compatible with the pullback** along an automorphism
`e` of a connected `S`: `e^* x ⌣ e^* y = e^*(x ⌣ y)`. -/
theorem adicConstantCup_pullback [ConnectedSpace S] (e : S ≅ S) (i j k : ℕ) (h : i + j = k)
    (x : AdicConstantH l S i) (y : AdicConstantH l S j) :
    adicConstantCup hfin hc i j k h (adicConstantHPullback l e i x)
        (adicConstantHPullback l e j y) =
      adicConstantHPullback l e k (adicConstantCup hfin hc i j k h x y) := by
  have := congrArg (fun φ ↦ φ x y) ((isBaseChange_integralToAdicConstantH l S i).algHom_ext
    ((adicConstantCup hfin hc i j k h).compl₁₂ (adicConstantHPullback l e i)
      (adicConstantHPullback l e j))
    ((adicConstantCup hfin hc i j k h).compr₂ (adicConstantHPullback l e k)) fun a ↦
      (isBaseChange_integralToAdicConstantH l S j).algHom_ext _ _ fun b ↦ by
        simp only [LinearMap.compl₁₂_apply, LinearMap.compr₂_apply,
          adicConstantHPullback_integralToAdicConstantH, adicConstantCup_integralToAdicConstantH,
          integralAdicCup_pullback])
  simpa using this

end Rational

end AlgebraicGeometry.ProEtale
