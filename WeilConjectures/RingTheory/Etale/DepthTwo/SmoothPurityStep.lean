/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.RingTheory.Etale.DepthTwo.SmoothPurityDiagonal
public import WeilConjectures.RingTheory.Etale.DepthTwo.SmoothPurityLocal
public import WeilConjectures.RingTheory.Etale.DepthTwo.LocalToGlobal
public import WeilConjectures.RingTheory.IntegrallyClosed.RegularPairAvoid
public import WeilConjectures.RingTheory.Smooth.IntegrallyClosed
public import Mathlib.RingTheory.Localization.BaseChange

/-!
# The local step of purity for normal covers of a smooth algebra

Let `R₀` be a Noetherian integrally closed domain, `q ≠ 0` a prime of `R₀`, `B` a smooth
`R₀`-algebra, `M` a `B`-algebra in which the nonzero elements of `R₀` are invertible and `T` the
integral closure of `B` in `M`. Let `P` be a prime of `B` over `q` which is not minimal over
`qB`. If `T` is finite étale over a neighbourhood of every prime `Q ⊊ P`, then `B_P ⊗_B T` is
finite étale over `B_P` (`RingTheory.DepthTwo.etale_finite_localization_of_smooth`).

Proof. Let `O = B_P`, a Noetherian normal local domain. The kernel `𝔭` of `O → (κ(q) ⊗ B)_P` is a
prime strictly between `0` and the maximal ideal (as `P` is not minimal over `qB`), so `O` has
dimension at least two, and for `0 ≠ a ∈ q` there is `b ∉ 𝔭` with `[a, b]` regular
(`IsIntegrallyClosed.exists_isWeaklyRegular_pair_of_not_le`). The integral closure is finite étale
over `D(a)` and `D(b)` (these lie in the punctured spectrum), hence finite with `(a, b)` regular
on it (`RingTheory.DepthTwo.finite_and_isRegularPair_integralClosure`), and étale by
`RingTheory.DepthTwo.etale_of_smooth_of_diagonal`.

This is a step of the proof of purity for normal covers of a smooth algebra over a normal base
(`RingTheory.DepthTwo.exists_etale_integralClosure_of_smooth`), an input of blueprint
`sbc-thm-spreading-finite-etale-galois`.
-/

@[expose] public section

universe u

open TensorProduct IsLocalRing

namespace Algebra

variable {D X : Type u} [CommRing D] [CommRing X] [Algebra D X]

/-- **Finite étale algebras are local on the base** (without a rank bound). -/
theorem etale_finite_of_span_eq_top' (s : Set D) (hs : Ideal.span s = ⊤)
    (H : ∀ g ∈ s, Algebra.Etale (Localization.Away g) (Localization.Away g ⊗[D] X) ∧
      Module.Finite (Localization.Away g) (Localization.Away g ⊗[D] X)) :
    Algebra.Etale D X ∧ Module.Finite D X := by
  refine ⟨RingHom.etale_algebraMap.mp (RingHom.Etale.ofLocalizationSpan (algebraMap D X) s hs
      fun g ↦ etale_awayMap_of_etale_tensor g.1 (H g.1 g.2).1), ?_⟩
  exact Module.Finite.of_localizationSpan' s hs
    (Rₚ := fun g ↦ Localization.Away g.1) (Mₚ := fun g ↦ Localization.Away g.1 ⊗[D] X)
    (fun g ↦ TensorProduct.mk D _ X 1) fun g ↦ (H g.1 g.2).2

/-- **Finite étale base changes, locally** (without a rank bound). If elements `h` of `B` with
`B_h ⊗_B T₀` finite étale over `B_h` cover `Spec D` (through `B → D`), then `D ⊗_B T₀` is finite
étale over `D`. -/
theorem etale_finite_tensor_of_forall_isPrime' {B D T₀ : Type u} [CommRing B] [CommRing D]
    [CommRing T₀] [Algebra B D] [Algebra B T₀]
    (H : ∀ Q : Ideal D, Q.IsPrime → ∃ h : B, algebraMap B D h ∉ Q ∧
      Algebra.Etale (Localization.Away h) (Localization.Away h ⊗[B] T₀) ∧
      Module.Finite (Localization.Away h) (Localization.Away h ⊗[B] T₀)) :
    Algebra.Etale D (D ⊗[B] T₀) ∧ Module.Finite D (D ⊗[B] T₀) := by
  let s : Set D := {g | ∃ h : B, g = algebraMap B D h ∧
    Algebra.Etale (Localization.Away h) (Localization.Away h ⊗[B] T₀) ∧
    Module.Finite (Localization.Away h) (Localization.Away h ⊗[B] T₀)}
  have hs : Ideal.span s = ⊤ := by
    by_contra hne
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
    obtain ⟨h, hQ, hE⟩ := H m hm.isPrime
    exact hQ (hle (Ideal.subset_span ⟨h, rfl, hE⟩))
  refine etale_finite_of_span_eq_top' s hs ?_
  rintro _ ⟨h, rfl, hE, hF⟩
  let Bh := Localization.Away h
  let Dg := Localization.Away (algebraMap B D h)
  let : Algebra Bh Dg := (Localization.awayMap (algebraMap B D) h).toAlgebra
  have : IsScalarTower B Bh Dg := IsScalarTower.of_algebraMap_eq fun b ↦ by
    rw [RingHom.algebraMap_toAlgebra, Localization.awayMap, IsLocalization.Away.map,
      IsLocalization.map_eq, IsScalarTower.algebraMap_apply B D Dg]
  let e : Dg ⊗[Bh] (Bh ⊗[B] T₀) ≃ₐ[Dg] Dg ⊗[D] (D ⊗[B] T₀) :=
    (Algebra.TensorProduct.cancelBaseChange B Bh Dg Dg T₀).trans
      (Algebra.TensorProduct.cancelBaseChange B D Dg Dg T₀).symm
  exact ⟨.of_equiv e, .equiv e.toLinearEquiv⟩

end Algebra

namespace RingTheory.DepthTwo

variable {R₀ B M : Type u} [CommRing R₀] [IsDomain R₀] [IsIntegrallyClosed R₀]
  [IsNoetherianRing R₀] [CommRing B] [Algebra R₀ B] [Algebra.Smooth R₀ B]
  [CommRing M] [Algebra B M] [Algebra R₀ M] [IsScalarTower R₀ B M]

/-- **The local step of purity for normal covers of a smooth algebra.** See the module
docstring. -/
theorem etale_finite_localization_of_smooth (q : Ideal R₀) [q.IsPrime] (hq : q ≠ ⊥)
    (hunit : ∀ r : R₀, r ≠ 0 → IsUnit (algebraMap R₀ M r)) (P : Ideal B) [P.IsPrime]
    (hP : q = P.comap (algebraMap R₀ B)) (hmin : P ∉ (q.map (algebraMap R₀ B)).minimalPrimes)
    (H : ∀ Q : Ideal B, Q.IsPrime → Q < P →
      ∃ h ∉ Q, Algebra.Etale (Localization.Away h) (Localization.Away h ⊗[B] integralClosure B M) ∧
        Module.Finite (Localization.Away h) (Localization.Away h ⊗[B] integralClosure B M)) :
    Algebra.Etale (Localization.AtPrime P) (Localization.AtPrime P ⊗[B] integralClosure B M) ∧
      Module.Finite (Localization.AtPrime P) (Localization.AtPrime P ⊗[B] integralClosure B M) := by
  sorry

end RingTheory.DepthTwo
