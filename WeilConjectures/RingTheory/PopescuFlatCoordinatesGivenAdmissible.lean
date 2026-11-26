/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.PopescuAdmissibleSubalgebra
public import WeilConjectures.RingTheory.GRing
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.Algebra.MvPolynomial.Basic

import WeilConjectures.RingTheory.PopescuSolutionModuloChoose
import WeilConjectures.RingTheory.PopescuAppendFlatParameters
import Mathlib.LinearAlgebra.Basis.Basic

/-!
# Flat coordinates in an enlargement of a given admissible subalgebra

Given an admissible subalgebra `A₀`, we find an admissible `A ≥ A₀` together with flat
polynomial coordinates mapping into `A` whose residue differentials span.

## References

* [Stacks, Tag 07FH] (proof, through property (1)), together with the corrected enlargement
  lemma `exists_popescu_admissible_differential_basis`
-/

@[expose] public section
set_option autoImplicit false
universe u v
namespace Algebra

/-- Flat coordinates in an admissible enlargement of a specified admissible subalgebra. -/
theorem exists_popescu_flat_coordinates_given_admissible
    (k : Type u) (Λ : Type v) [Field k] [CommRing Λ] [Algebra k Λ]
    [IsNoetherianRing Λ] (p : ℕ) [CharP k p] (hp : 0 < p)
    (hreg : IsGeometricallyRegular k Λ) (q : Ideal Λ) [q.IsPrime]
    (n : ℕ) (hn : 1 ≤ n)
    (A₀ : Subalgebra k (Localization.AtPrime q ⧸
      (q.map (algebraMap Λ (Localization.AtPrime q))) ^ n)) (_ : IsLocalRing A₀)
    (hA₀ : A₀.IsPopescuAdmissible ((q.map (algebraMap Λ (Localization.AtPrime q))).map
      (Ideal.Quotient.mk ((q.map (algebraMap Λ (Localization.AtPrime q))) ^ n)))) :
    ∃ (A : Subalgebra k (Localization.AtPrime q ⧸
        (q.map (algebraMap Λ (Localization.AtPrime q))) ^ n)) (_ : IsLocalRing A),
      A.IsPopescuAdmissible ((q.map (algebraMap Λ (Localization.AtPrime q))).map
        (Ideal.Quotient.mk ((q.map (algebraMap Λ (Localization.AtPrime q))) ^ n))) ∧
      IsLocalRing.maximalIdeal A = Ideal.comap A.val.toRingHom
        ((q.map (algebraMap Λ (Localization.AtPrime q))).map
          (Ideal.Quotient.mk ((q.map (algebraMap Λ (Localization.AtPrime q))) ^ n))) ∧
      A₀ ≤ A ∧
      ∃ (m : ℕ) (φ : MvPolynomial (Fin m) k →ₐ[k] Λ)
        (ψ : Localization.AtPrime (q.comap φ.toRingHom) →+* Localization.AtPrime q),
        ψ.comp (algebraMap (MvPolynomial (Fin m) k)
            (Localization.AtPrime (q.comap φ.toRingHom))) =
          (algebraMap Λ (Localization.AtPrime q)).comp φ.toRingHom ∧
        q.map (algebraMap Λ (Localization.AtPrime q)) =
          (q.comap φ.toRingHom).map
            ((algebraMap Λ (Localization.AtPrime q)).comp φ.toRingHom) ∧
        ψ.Flat ∧
        ∃ a : Fin m → A,
          (∀ j, (a j : Localization.AtPrime q ⧸
            (q.map (algebraMap Λ (Localization.AtPrime q))) ^ n) =
            Ideal.Quotient.mk ((q.map (algebraMap Λ (Localization.AtPrime q))) ^ n)
              (algebraMap Λ (Localization.AtPrime q) (φ (MvPolynomial.X j)))) ∧
          Submodule.span (IsLocalRing.ResidueField A)
            (Set.range (fun j ↦ KaehlerDifferential.D k (IsLocalRing.ResidueField A)
              (IsLocalRing.residue A (a j)))) = ⊤ := by
  classical
  obtain ⟨A, hAloc, hinc, hA, hmax, ι, _hinj, hcompat,
    t, r, xs, ys, a, a', ha, ha', ⟨b, hb⟩, hys⟩ :=
    exists_popescu_admissible_differential_basis k Λ p hp hreg q n hn A₀ hA₀
  let : IsLocalRing A := hAloc
  let : EssFiniteType k A := hA.2.1
  let : EssFiniteType k (IsLocalRing.ResidueField A) :=
    EssFiniteType.comp k A (IsLocalRing.ResidueField A)
  obtain ⟨e, s, ψ, hcomp, hideal, hflat⟩ :=
    exists_popescu_append_flat_parameters k Λ p hp hreg q (IsLocalRing.ResidueField A)
      ι t r xs ys (fun j ↦ IsLocalRing.residue A (a j))
      (fun j ↦ hcompat (a j) _ (ha j)) b hb (fun i ↦ (ha' i).1) hys
  let φ : MvPolynomial (Fin (t + e)) k →ₐ[k] Λ :=
    MvPolynomial.aeval (Fin.addCases xs (fun i ↦ ys (s i)))
  refine ⟨A, hAloc, hA, hmax, hinc, t + e, φ, ψ, hcomp, hideal, hflat,
    Fin.addCases a (fun i ↦ a' (s i)), ?_, ?_⟩
  · intro j
    refine Fin.addCases (fun i ↦ ?_) (fun i ↦ ?_) j
    · simpa [φ] using ha i
    · simpa [φ] using (ha' (s i)).2
  · apply top_unique
    rw [← b.span_eq]
    apply Submodule.span_mono
    rintro _ ⟨j, rfl⟩
    refine ⟨Fin.castAdd e j, ?_⟩
    simpa using (hb j).symm


end Algebra
