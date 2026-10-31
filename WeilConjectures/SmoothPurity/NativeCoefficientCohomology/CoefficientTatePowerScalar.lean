/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.FrobeniusCoefficientTwists.FrobeniusCoefficientTwistsCanonical
public import WeilConjectures.SmoothPurity.NativeCoefficientCohomology.CoefficientRootScalarBasis

/-! # Multiplication on the normalized positive root tensors -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures.NativeCoefficientCohomology
open FrobeniusCoefficientTwists

private theorem integral_root_tensor_nsmul
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (S : Scheme.{u}) (U : S.ProEtᵒᵖ)
    (x : (purTwistZlOne S l).obj.obj U) (q : ℕ) :
    purTwistIntegralTensor S l E U 1 (q • x) =
      q • purTwistIntegralTensor S l E U 1 x := by
  induction q with
  | zero => simp only [zero_nsmul, purTwistIntegralTensor, TensorProduct.tmul_zero, map_zero]
  | succ q ih =>
    rw [succ_nsmul]
    unfold purTwistIntegralTensor at ih ⊢
    rw [TensorProduct.tmul_add, map_add, ih, succ_nsmul]

private theorem tensor_nsmul_first
    (S : Scheme.{u}) (R : Sheaf (ProEt.topology S) CommRingCat.{u + 1})
    (M N : SheafOfModules.{u + 1} (purTwistRing S R)) (U : S.ProEtᵒᵖ)
    (x : M.val.obj U) (y : N.val.obj U) (q : ℕ) :
    SheafOfModules.siteSheafTensorTmul M N U (q • x) y =
      q • SheafOfModules.siteSheafTensorTmul M N U x y := by
  dsimp only [SheafOfModules.siteSheafTensorTmul]
  induction q with
  | zero => simp only [zero_nsmul, TensorProduct.zero_tmul, map_zero]
  | succ q ih => rw [succ_nsmul, TensorProduct.add_tmul, map_add, ih, succ_nsmul]

private theorem tensor_nsmul_second
    (S : Scheme.{u}) (R : Sheaf (ProEt.topology S) CommRingCat.{u + 1})
    (M N : SheafOfModules.{u + 1} (purTwistRing S R)) (U : S.ProEtᵒᵖ)
    (x : M.val.obj U) (y : N.val.obj U) (q : ℕ) :
    SheafOfModules.siteSheafTensorTmul M N U x (q • y) =
      q • SheafOfModules.siteSheafTensorTmul M N U x y := by
  dsimp only [SheafOfModules.siteSheafTensorTmul]
  induction q with
  | zero => simp only [zero_nsmul, TensorProduct.tmul_zero, map_zero]
  | succ q ih => rw [succ_nsmul, TensorProduct.tmul_add, map_add, ih, succ_nsmul]

private theorem positive_generator_nsmul
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (S : Scheme.{u}) (U : S.ProEtᵒᵖ)
    (a : (completedIntegralCoefficientSheafUnrestricted l E S).obj.obj U)
    (q : ℕ) : ∀ (d : ℕ) (x : Fin d → (purTwistZlOne S l).obj.obj U),
      generator l E S U a d (fun i ↦ q • x i) =
        q ^ d • generator l E S U a d x := by
  apply Nat.twoStepInduction
  · intro x
    simp only [generator, pow_zero, one_nsmul]
  · intro x
    simp only [generator, pow_one]
    rw [integral_root_tensor_nsmul]
    exact (DistribSMul.toAddMonoidHom _ a).map_nsmul q _
  · intro d _ ih x
    change SheafOfModules.siteSheafTensorTmul
      (positiveLine l E S (d + 1)) (purTwistIntegralModule S l E) U
      (generator l E S U a (d + 1) (fun i ↦ q • x i.castSucc))
      (purTwistIntegralTensor S l E U 1 (q • x (Fin.last (d + 1)))) = _
    rw [ih, integral_root_tensor_nsmul,
      tensor_nsmul_first, tensor_nsmul_second, smul_smul, ← pow_succ]
    rfl

/-- A q-scaled equation for first root sections gives the q^d-scaled equation
on every normalized pure generator of the positive coefficient Tate line.

Source: Weil I (2.2), ordered tensor powers in the coefficient Tate convention.
(blueprint: lem-sf-coefficient-tate-power-scalar)

Proof: the integral first-root tensor is additive in its root argument. The
sheaf tensor is additive in each factor. Induction on the ordered tensor power
therefore multiplies the scalar q once per root factor, yielding q^d. Substitute
the defining root-normalized formula for the positive Frobenius map, and replace
each q-scaled transported root with its prescribed target root. The zeroth power
has no root factors and scalar one. The argument works for q=0 and empty sites. -/
theorem coefficient_tate_power_scalar
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] {S : Scheme.{u}} (g : S ⟶ S) [IsIso g]
    (q d : ℕ) (V : S.ProEt)
    (a : (completedIntegralCoefficientSheafUnrestricted l E S).obj.obj (op V))
    (x : Fin d → (purTwistZlOne S l).obj.obj (op V))
    (y : Fin d → (purTwistZlOne S l).obj.obj (op ((proEtaleBaseChange g).obj V)))
    (h : ∀ i, q • rootSection l g V (x i) = y i) :
    q ^ d • ((positiveLineMaps l E g d).hom.val.app
      (op ((proEtaleBaseChange g).obj V))
        (moduleSection l E g (positiveLine l E S d) V
          (generator l E S (op V) a d x))) =
      generator l E S (op ((proEtaleBaseChange g).obj V))
        ((sfCompletedCoefficientMap l E g).hom.app (op V) a) d y := by
  have hn := (existsUnique_positiveLineMaps l E g).exists.choose_spec d V a x
  change (positiveLineMaps l E g d).hom.val.app _ _ = _ at hn
  rw [hn, ← positive_generator_nsmul]
  congr 1
  funext i
  exact h i

/-- The positive-power scalar formula expressed entirely in finite frame coordinates.
Source: Weil I (2.2) (blueprint: lem-sf-coefficient-tate-power-scalar). -/
abbrev CoefficientTateFramePowerScalarLaw
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] {S : Scheme.{u}} (g : S ⟶ S) [IsIso g]
    (q : ℕ) (A : CoefficientTateRootFrames S l q g) : Prop :=
  ∀ (d : ℕ) (V : S.ProEt)
    (a : (completedIntegralCoefficientSheafUnrestricted l E S).obj.obj (op V))
    (x : Fin d → (purTwistZlOne S l).obj.obj (op V))
    (y : Fin d → (purTwistZlOne S l).obj.obj (op ((proEtaleBaseChange g).obj V)))
    (c : Fin d → ℕ → ℕ),
    (∀ i n,
      (limit.π (proEtaleRootsOfUnityTower S l (Fact.out : l.Prime)) (op n)).hom.app
          (op V) (x i) =
        (A.basis (n + 1)).hom.hom.app (op V)
          (coefficientRootSection S (l ^ (n + 1)) (op V) (c i n))) →
    (∀ i n,
      (limit.π (proEtaleRootsOfUnityTower S l (Fact.out : l.Prime)) (op n)).hom.app
          (op ((proEtaleBaseChange g).obj V)) (y i) =
        (A.basis (n + 1)).hom.hom.app (op ((proEtaleBaseChange g).obj V))
          (coefficientRootSection S (l ^ (n + 1))
            (op ((proEtaleBaseChange g).obj V)) (c i n))) →
      q ^ d • ((positiveLineMaps l E g d).hom.val.app
        (op ((proEtaleBaseChange g).obj V))
          (moduleSection l E g (positiveLine l E S d) V
            (generator l E S (op V) a d x))) =
        generator l E S (op ((proEtaleBaseChange g).obj V))
          ((sfCompletedCoefficientMap l E g).hom.app (op V) a) d y

/-- Finite normalized root frames supply the normalized positive-power scalar law.
Source: Weil I (2.2) (blueprint: lem-sf-coefficient-tate-power-scalar).
Proof: project each root section to the finite frame. Joint injectivity of the
limit projections gives its q-scaled equation. Apply the pure-generator power
calculation to the d equations. Empty lists give degree zero without exceptions. -/
theorem coefficient_tate_frame_power_scalar_law
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] {S : Scheme.{u}} (g : S ⟶ S) [IsIso g]
    (q : ℕ) (A : CoefficientTateRootFrames S l q g) :
    CoefficientTateFramePowerScalarLaw l E g q A := by
  intro d V a x y c hx hy
  apply coefficient_tate_power_scalar l E g q d V a x y
  intro i
  exact A.limit_scalar S l q g V (x i) (y i) (c i) (hx i) (hy i)

end WeilConjectures.NativeCoefficientCohomology
