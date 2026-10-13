/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U1
-/
module

public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.Data.Set.Card
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
import Sheaf.RingTheory.EtaleComplementIsolatedCount
import Mathlib.RingTheory.Localization.Away.Lemmas
import Mathlib.RingTheory.Etale.QuasiFinite

/-!
# Removing one isolated point of a fibre by an étale extension

Source: Stacks Project, Algebra, Tag 00UK, induction step using Tag 00UJ
(blueprint: lem-weil-pbc-etale-isolated-point-removal).
-/

@[expose] public section

universe u v

open scoped TensorProduct

namespace Algebra

/-- (blueprint: lem-weil-pbc-etale-isolated-point-removal)
Source: Stacks Project, Algebra, Tag 00UK, proof, the one-point splitting and decrease
of the number of isolated fibre points, using Tag 00UJ.

Proof: A positive cardinal supplies an isolated point of the fibre. Its inverse image
under `PrimeSpectrum.preimageHomeomorphFiber` is a quasi-finite prime over `p`.
Apply the one-prime étale splitting of Tag 00UJ. Its idempotent `e` splits the
base-changed algebra into the actual quotient rings `A = C/(1-e)` and `D = C/(e)`.
The first is isomorphic to `C[e⁻¹]`, hence finite by 00UJ. The second is finite type
by base change and quotient. The unchanged
residue field identifies the spectrum of the new fibre with the old one. The fibre
of `D` is a clopen subspace of this spectrum, whose isolated points are therefore
isolated points of the original spectrum. It omits the selected point, which lies
in the `e` factor. This gives an injection of its isolated points into the original
finite set minus the selected point, hence a strictly smaller cardinal. The set is
finite because its cardinal was assumed positive. No induction or simultaneous
removal of the other isolated points is used here. -/
theorem exists_etale_finiteFactor_smaller_fibre
    {R : Type u} {S : Type (max u v)} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FiniteType R S] (p : Ideal R) [p.IsPrime]
    (hpos : 0 < {q : PrimeSpectrum (p.Fiber S) |
      IsOpen ({q} : Set (PrimeSpectrum (p.Fiber S)))}.ncard) :
    ∃ (R₁ : Type u) (_ : CommRing R₁) (_ : Algebra R R₁) (_ : Algebra.Etale R R₁)
      (P : Ideal R₁) (_ : P.IsPrime) (_ : P.LiesOver p)
      (A : Type (max u v)) (_ : CommRing A) (_ : Algebra R₁ A)
      (D : Type (max u v)) (_ : CommRing D) (_ : Algebra R₁ D)
      (_ : Algebra.FiniteType R₁ D),
      Function.Bijective (Ideal.ResidueField.mapₐ p P (Algebra.ofId R R₁) (P.over_def p)) ∧
      Nonempty ((R₁ ⊗[R] S) ≃ₐ[R₁] (A × D)) ∧ Module.Finite R₁ A ∧
      {q : PrimeSpectrum (P.Fiber D) | IsOpen ({q} : Set (PrimeSpectrum (P.Fiber D)))}.ncard <
        {q : PrimeSpectrum (p.Fiber S) |
          IsOpen ({q} : Set (PrimeSpectrum (p.Fiber S)))}.ncard := by
  classical
  obtain ⟨z, hz⟩ := (Set.ncard_pos (Set.finite_of_ncard_pos hpos)).mp hpos
  let q := (PrimeSpectrum.preimageHomeomorphFiber R S ⟨p, inferInstance⟩).symm z
  let : q.1.asIdeal.LiesOver p := ⟨congrArg PrimeSpectrum.asIdeal q.2.symm⟩
  let : Algebra.QuasiFiniteAt p.ResidueField z.asIdeal :=
    Algebra.QuasiFiniteAt.of_isOpen_singleton z hz
  let : Algebra.QuasiFiniteAt R q.1.asIdeal :=
    Algebra.QuasiFiniteAt.of_quasiFiniteAt_residueField p q.1.asIdeal z.asIdeal rfl
  obtain ⟨R₁, hR₁, hRR₁, hE₁, P, hP, hPp, e, he, r, hr, hrP,
    hrq, her, hres, hfinite, _⟩ :=
    Algebra.exists_etale_isIdempotentElem_forall_liesOver_eq p q.1.asIdeal
  let := hR₁
  let := hRR₁
  let := hE₁
  let := hP
  let := hPp
  let := hr
  let := hrP
  let C := R₁ ⊗[R] S
  let A := C ⧸ Ideal.span {1 - e}
  let D := C ⧸ Ideal.span {e}
  let : IsLocalization.Away e A := IsLocalization.Away.quotient_of_isIdempotentElem he
  let f : Localization.Away e ≃ₐ[R₁] A :=
    (IsLocalization.algEquiv (.powers e) (Localization.Away e) A).restrictScalars R₁
  let : Module.Finite R₁ (Localization.Away e) := hfinite
  have hfiniteA : Module.Finite R₁ A := Module.Finite.equiv f.toLinearEquiv
  refine ⟨R₁, hR₁, hRR₁, hE₁, P, hP, hPp, A, inferInstance, inferInstance,
    D, inferInstance, inferInstance, inferInstance, hres, ?_, hfiniteA, ?_⟩
  · exact ⟨AlgEquiv.prodQuotientOfIsIdempotentElem R₁ he.one_sub he
      (sub_add_cancel 1 e) (by rw [sub_mul, one_mul, he.eq]; simp)⟩
  · exact fibre_ncard_quotient_idempotent_lt p P hres e he q.1.asIdeal r hrq her

end Algebra
