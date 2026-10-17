/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.RingTheory.Etale.KummerDescent
public import WeilConjectures.RingTheory.Invariant.TensorIntegralClosure

/-!
# Descent of étaleness of an integral closure along a tame Kummer cover

Let `R` be a Noetherian local ring, `π` in its maximal ideal, `n` invertible in `R`, `ζ ∈ R` with
`ζⁿ = 1` and `1 - ζⁱ` a unit for `0 < i < n`, and `R' = R[t] ⧸ (tⁿ - π)` with the Kummer action
of `ZMod n`. Let `M` be an `R`-algebra and `T'` the integral closure of `R'` in `R' ⊗[R] M`. If
`T'` is finite étale over `R'` and its closed fibre is split by `k ≥ rank T'` distinct invariant
points, then the integral closure of `R` in `M` is finite étale over `R`
(`RingTheory.InvariantsDescent.etale_and_finite_integralClosure_of_kummer`).

This is the descent step of the trait case of blueprint `sbc-thm-spreading-finite-etale-galois`
([Stacks 0EYJ]).
-/

@[expose] public section

open Polynomial IsLocalRing TensorProduct

namespace RingTheory.InvariantsDescent

set_option maxHeartbeats 1600000 in
/-- **Descent of étaleness of an integral closure along a tame Kummer cover.** See the module
docstring. -/
theorem etale_and_finite_integralClosure_of_kummer {R : Type*} [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] (n : ℕ) [NeZero n] (π : R) [Fact (π ∈ maximalIdeal R)] {ζ : R}
    (hζ : ζ ^ n = 1) (hu : ∀ i, 0 < i → i < n → IsUnit (1 - ζ ^ i)) (hn : IsUnit (n : R))
    {M : Type*} [CommRing M] [Algebra R M]
    (hinj : Function.Injective (Algebra.TensorProduct.includeRight :
      M →ₐ[R] AdjoinRoot (X ^ n - C π) ⊗[R] M))
    [Algebra.Etale (AdjoinRoot (X ^ n - C π))
      (integralClosure (AdjoinRoot (X ^ n - C π)) (AdjoinRoot (X ^ n - C π) ⊗[R] M))]
    [Module.Finite (AdjoinRoot (X ^ n - C π))
      (integralClosure (AdjoinRoot (X ^ n - C π)) (AdjoinRoot (X ^ n - C π) ⊗[R] M))]
    {k : ℕ} (hk : Module.finrank (AdjoinRoot (X ^ n - C π))
      (integralClosure (AdjoinRoot (X ^ n - C π)) (AdjoinRoot (X ^ n - C π) ⊗[R] M)) ≤ k)
    (φ : Fin k → (integralClosure (AdjoinRoot (X ^ n - C π)) (AdjoinRoot (X ^ n - C π) ⊗[R] M)
      →ₐ[AdjoinRoot (X ^ n - C π)] ResidueField (AdjoinRoot (X ^ n - C π))))
    (hφ : Function.Injective φ)
    (hφΓ : letI := AdjoinRoot.kummerAction n π hζ
      haveI : SMulCommClass (Multiplicative (ZMod n)) R (AdjoinRoot (X ^ n - C π)) :=
        AdjoinRoot.smulCommClass_kummerAction n π hζ
      ∀ j (g : Multiplicative (ZMod n)) t, φ j (Algebra.IsInvariant.integralClosureMap (R := R)
        (R' := AdjoinRoot (X ^ n - C π)) (M := M) (Multiplicative (ZMod n)) g t) = φ j t) :
    Algebra.Etale R (integralClosure R M) ∧ Module.Finite R (integralClosure R M) := by
  let R' := AdjoinRoot (X ^ n - C π)
  let T' := integralClosure R' (R' ⊗[R] M)
  let T := integralClosure R M
  let Γ := Multiplicative (ZMod n)
  letI := AdjoinRoot.kummerAction n π hζ
  haveI : SMulCommClass Γ R R' := AdjoinRoot.smulCommClass_kummerAction n π hζ
  haveI : Algebra.IsInvariant R R' Γ := AdjoinRoot.isInvariant_kummerAction n π hζ hu
  letI := Algebra.IsInvariant.tensorAction (R := R) (R' := R') (M := M) Γ
  letI := Algebra.IsInvariant.integralClosureAction (R := R) (R' := R') (M := M) Γ
  -- the map `T → T'`
  have hmemT (t : T) : Algebra.TensorProduct.includeRight (t : M) ∈ T' :=
    (t.2.map (Algebra.TensorProduct.includeRight : M →ₐ[R] R' ⊗[R] M)).tower_top
  let ι : T →+* T' :=
    { toFun t := ⟨_, hmemT t⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' x y := Subtype.ext (map_mul _ _ _)
      map_zero' := Subtype.ext (map_zero _)
      map_add' x y := Subtype.ext (map_add _ _ _) }
  letI : Algebra T T' := ι.toAlgebra
  have hι (t : T) : ((algebraMap T T' t : T') : R' ⊗[R] M) =
      Algebra.TensorProduct.includeRight (t : M) := rfl
  have : IsScalarTower R T T' := .of_algebraMap_eq fun r ↦ Subtype.ext <| by
    rw [hι]
    simp [Algebra.algebraMap_eq_smul_one, Algebra.TensorProduct.one_def, TensorProduct.smul_tmul']
  have : SMulCommClass Γ T T' := ⟨fun g t x ↦ Subtype.ext <| by
    rw [Algebra.smul_def, Algebra.smul_def, smul_mul', Subalgebra.coe_mul, Subalgebra.coe_mul,
      Algebra.IsInvariant.coe_integralClosureAction_smul, hι]
    congr 1
    simp [Algebra.IsInvariant.tensorAction_smul_def, Algebra.IsInvariant.tensorAlgAut]⟩
  have : Algebra.IsInvariant T T' Γ := ⟨fun x hx ↦ by
    obtain ⟨t, ht⟩ := Algebra.IsInvariant.exists_eq_includeRight_of_forall_smul_eq_integralClosure
      (by simpa [Γ, ZMod.card] using hn) hinj x hx
    exact ⟨t, Subtype.ext ht⟩⟩
  have hdist : SMulDistribClass Γ R' T' := ⟨fun g r x ↦ Subtype.ext <| by
    rw [Algebra.smul_def, Algebra.smul_def, smul_mul']
    rfl⟩
  have hT : Function.Injective (algebraMap T T') := fun x y h ↦
    Subtype.ext (hinj congr(Subtype.val $h))
  exact etale_and_finite_of_kummer n π hζ hu hn hdist hT hk φ hφ hφΓ

end RingTheory.InvariantsDescent
