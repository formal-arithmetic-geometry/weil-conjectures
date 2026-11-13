/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.RingTheory.Kaehler.Basic
public import WeilConjectures.FieldTheory.SeparableExtension
import Mathlib.RingTheory.Smooth.Field

/-!
# Separable residue field: the cotangent space injects into the differentials

## References

* [Stacks Project, Tag 00TU](https://stacks.math.columbia.edu/tag/00TU)
-/

@[expose] public section

universe u v

open scoped TensorProduct

namespace Algebra

/-- For a Noetherian local `k`-algebra with residue field finitely generated as a field
and separable over `k`,
the cotangent space injects into the base-changed Kähler differentials.

The tensor factors are reversed relative to the source: tensor symmetry takes
`1 ⊗ d a` to `d a ⊗ 1`, so injectivity is unchanged. -/
theorem separable_residue_cotangent_injective
    (k : Type u) (R : Type v) [Field k] [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] [Algebra k R]
    (hfg : (⊤ : IntermediateField k (IsLocalRing.ResidueField R)).FG)
    (hsep : Algebra.IsSeparableExtension k (IsLocalRing.ResidueField R)) :
    Function.Injective
      ((KaehlerDifferential.kerCotangentToTensor k R (IsLocalRing.ResidueField R)).comp
        (Ideal.Cotangent.equivOfEq (IsLocalRing.maximalIdeal R)
          (RingHom.ker (algebraMap R (IsLocalRing.ResidueField R)))
          IsLocalRing.ker_residue.symm).toLinearMap) := by
  classical
  let K := IsLocalRing.ResidueField R
  obtain ⟨s, hs, hseps⟩ := hsep ⊤ hfg
  have hseps' : Algebra.IsSeparable
      (IntermediateField.adjoin k (Set.range ((↑) : s → (⊤ : IntermediateField k K))))
      (⊤ : IntermediateField k K) := by
    have hr : Set.range ((↑) : s → (⊤ : IntermediateField k K)) = s := by
      exact Subtype.range_coe_subtype
    rw [hr]
    exact hseps
  have : FormallySmooth k (⊤ : IntermediateField k K) :=
    FormallySmooth.of_algebraicIndependent_of_isSeparable hs.1
  have : FormallySmooth k K := FormallySmooth.of_equiv IntermediateField.topEquiv
  let f := IsScalarTower.toAlgHom k R K
  have hf : Function.Surjective f := IsLocalRing.residue_surjective
  have hq : Function.Surjective f.kerSquareLift :=
    Ideal.Quotient.lift_surjective_of_surjective _ _ hf
  have hn : IsNilpotent (RingHom.ker f.kerSquareLift.toRingHom) := by
    exact ⟨2, by rw [AlgHom.ker_kerSquareLift, Ideal.cotangentIdeal_square]; rfl⟩
  let σ := FormallySmooth.liftOfSurjective (AlgHom.id k K) f.kerSquareLift hq hn
  have hσ : f.kerSquareLift.comp σ = AlgHom.id k K :=
    FormallySmooth.comp_liftOfSurjective _ _ _ _
  obtain ⟨l, hl⟩ :=
    (retractionKerCotangentToTensorEquivSection (R := k) hf).symm ⟨σ, hσ⟩
  have hi : Function.Injective (KaehlerDifferential.kerCotangentToTensor k R K) := by
    apply Function.LeftInverse.injective (g := l)
    intro x
    exact LinearMap.congr_fun hl x
  exact hi.comp (Ideal.Cotangent.equivOfEq (IsLocalRing.maximalIdeal R)
    (RingHom.ker (algebraMap R K)) IsLocalRing.ker_residue.symm).injective

end Algebra
