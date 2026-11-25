/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import WeilConjectures.RingTheory.GRing
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Localization.FractionRing
import WeilConjectures.RingTheory.PolynomialResidueFiniteCoefficientModel
import WeilConjectures.RingTheory.PolynomialCompletedFibreCompatibleProduct
import WeilConjectures.RingTheory.FiniteOverCompleteLocalProduct

/-!
# Finite product presentation of extended polynomial formal fibres

A finite purely inseparable base change of a nonzero polynomial formal fibre above zero is a
finite product of linear-residue formal fibres over complete local domains.

## Implementation details

Clearing denominators of generators of `L / K` gives a finite `A`-subalgebra `B` of `L` with
fraction field `L`, which is complete local (Tag 0325). The kernel `s` of evaluation `B[X] → L`
has residue field `L`, and Tag 07N9 writes the completion base change as a product over the
primes above `q`; the factors at primes not containing `s` vanish. The empty product is allowed.
All rings `Bᵢ` lie in the universe of `L`, as subalgebras of `L`.

## References

* [Stacks, Tag 07PU] (first paragraph of the proof)
* [Stacks, Tag 0325]
* [Stacks, Tag 07N9]
-/

@[expose] public section

universe u

namespace Polynomial

set_option linter.unusedVariables false in
/-- A finite purely inseparable base change of a nonzero polynomial formal fibre above
zero is a finite product of linear-residue formal fibres over complete local domains.
This is a ring presentation, with no regularity assertion. -/
theorem formalFiber_finiteExtension_reduction
    (A : Type u) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (p : ℕ) (hp : p.Prime) [CharP (Localization.AtPrime (⊥ : Ideal A)) p]
    (q : Ideal (Polynomial A)) [q.IsMaximal]
    (hq : q.comap (Polynomial.C : A →+* Polynomial A) = IsLocalRing.maximalIdeal A)
    (r : Ideal (Polynomial A)) [r.IsPrime] (hrq : r ≤ q) (hr : r ≠ ⊥)
    (hrA : r.comap (Polynomial.C : A →+* Polynomial A) = ⊥)
    (L : Type u) [Field L] [Algebra r.ResidueField L]
    [Module.Finite r.ResidueField L] [IsPurelyInseparable r.ResidueField L] :
    let C := AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime q))
      (Localization.AtPrime q)
    ∃ (n : ℕ) (B : Fin n → Type u) (rings : ∀ i, CommRing (B i)),
      letI := rings
      ∃ (domains : ∀ i, IsDomain (B i)) (noeth : ∀ i, IsNoetherianRing (B i))
        (locals : ∀ i, IsLocalRing (B i)),
        letI := domains
        letI := noeth
        letI := locals
        ∃ (complete : ∀ i, IsAdicComplete (IsLocalRing.maximalIdeal (B i)) (B i))
          (q' : ∀ i, Ideal (Polynomial (B i))) (qmax : ∀ i, (q' i).IsMaximal)
          (s : ∀ i, Ideal (Polynomial (B i))) (sprime : ∀ i, (s i).IsPrime),
          letI := qmax
          letI := sprime
          (∀ i, IsFractionRing (B i) (s i).ResidueField) ∧
          (∀ i, (q' i).comap (Polynomial.C : B i →+* Polynomial (B i)) =
            IsLocalRing.maximalIdeal (B i)) ∧
          (∀ i, s i ≤ q' i) ∧ (∀ i, s i ≠ ⊥) ∧
          (∀ i, (s i).comap (Polynomial.C : B i →+* Polynomial (B i)) = ⊥) ∧
          Nonempty ((TensorProduct r.ResidueField L (r.Fiber C)) ≃+*
            (∀ i, (s i).Fiber
              (AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime (q' i)))
                (Localization.AtPrime (q' i))))) := by
  classical
  let : Algebra A L :=
    ((algebraMap r.ResidueField L).comp
      ((algebraMap (Polynomial A) r.ResidueField).comp Polynomial.C)).toAlgebra
  obtain ⟨B, hfin, s, hs, hsne, hsB, hfrac, e, he⟩ :=
    exists_finite_coefficient_model A r hr hrA L
  have : Module.Finite A B := hfin
  have : s.IsPrime := hs
  obtain ⟨hnoeth, hlocal, hcomplete, _⟩ :=
    (Algebra.finite_over_complete_local_product A B).2.2.2
      (inferInstance : IsDomain B)
  have : IsNoetherianRing B := hnoeth
  have : IsLocalRing B := hlocal
  have : IsAdicComplete (IsLocalRing.maximalIdeal B) B := hcomplete
  obtain ⟨n, q', qmax, hqB, hsq, hiso⟩ :=
    completed_fibre_compatible_product A B q hq r L s e he
  have : ∀ i, (q' i).IsMaximal := qmax
  refine ⟨n, fun _ ↦ B, fun _ ↦ inferInstance, fun _ ↦ inferInstance,
    fun _ ↦ hnoeth, fun _ ↦ hlocal, fun _ ↦ hcomplete,
    q', qmax, fun _ ↦ s, fun _ ↦ hs, ?_⟩
  exact ⟨fun _ ↦ hfrac, hqB, hsq, fun _ ↦ hsne, fun _ ↦ hsB, hiso⟩

end Polynomial
