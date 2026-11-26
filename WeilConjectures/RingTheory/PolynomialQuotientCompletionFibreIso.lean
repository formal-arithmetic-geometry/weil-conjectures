/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Polynomial.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.Noetherian.Basic
import WeilConjectures.RingTheory.CompletionSurjectiveBaseChange
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal

/-!
# Polynomial completion fibres under a coefficient quotient

For `T = S[X]_Q` and a prime `s`, quotienting the coefficients by `p = s ∩ S` identifies the fibre
of the completion of `T` at `s` with the corresponding fibre for `(S / p)[X]`.

## Implementation details

The quotient-localization identity identifies `(S / p)[X]_q` with `T / p T`, and completion of a
quotient (Tag 00MA) identifies its completion with the completion of `T` modulo `p`. Since `p`
annihilates the residue field, the tensor products agree. All maps come from universal
properties and are compatible with the scalars.

## References

* [Stacks, Tag 07PV]
* [Stacks, Tag 07PN]
* [Stacks, Tag 00CT]
* [Stacks, Tag 00MA]
* [Stacks, Tag 07BH]
-/

@[expose] public section

universe u

namespace Polynomial

/-- Quotienting the coefficients by the contraction of a localized prime preserves
its completion fibre, together with the residue-field scalar action. -/
theorem exists_quotient_completion_fibre_iso
    (S : Type u) [CommRing S] [IsNoetherianRing S]
    (Q : Ideal (Polynomial S)) [Q.IsMaximal]
    (s : Ideal (Localization.AtPrime Q)) [s.IsPrime]
    (p : Ideal S)
    (hp : p = (s.comap (algebraMap (Polynomial S) (Localization.AtPrime Q))).comap
      (Polynomial.C : S →+* Polynomial S))
    (q r : Ideal (Polynomial (S ⧸ p))) [q.IsMaximal] [r.IsPrime]
    (hq : q = Q.map (Polynomial.mapRingHom (Ideal.Quotient.mk p)))
    (hr : r = (s.comap (algebraMap (Polynomial S) (Localization.AtPrime Q))).map
      (Polynomial.mapRingHom (Ideal.Quotient.mk p))) :
    ∃ σ : r.ResidueField ≃+* s.ResidueField,
      ∃ e : r.Fiber (AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime q))
          (Localization.AtPrime q)) ≃+*
        s.Fiber (AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime Q))
          (Localization.AtPrime Q)),
        ∀ x a, e (x • a) = σ x • e a := by
  classical
  let R := Polynomial S
  let B := Polynomial (S ⧸ p)
  let T := Localization.AtPrime Q
  let D := Localization.AtPrime q
  let Cp := AdicCompletion (IsLocalRing.maximalIdeal T) T
  let Cq := AdicCompletion (IsLocalRing.maximalIdeal D) D
  let f : R →+* B := Polynomial.mapRingHom (Ideal.Quotient.mk p)
  have hf : Function.Surjective f := Polynomial.map_surjective _ Ideal.Quotient.mk_surjective
  let P := s.comap (algebraMap R T)
  have hP : P.IsPrime := Ideal.IsPrime.comap _
  let : P.IsPrime := hP
  have hk : RingHom.ker f ≤ P := by
    rw [Polynomial.ker_mapRingHom, Ideal.mk_ker, Ideal.map_le_iff_le_comap]
    exact le_of_eq hp
  have hc : P = r.comap f := by
    rw [hr, Ideal.comap_map_of_surjective f hf, ← RingHom.ker_eq_comap_bot]
    exact (sup_eq_left.mpr hk).symm
  have hQ : Q = q.comap f := by
    rw [hq, Ideal.comap_map_of_surjective f hf, ← RingHom.ker_eq_comap_bot]
    apply (sup_eq_left.mpr (hk.trans ?_)).symm
    intro x hx
    by_contra h
    exact (show s ≠ ⊤ from Ideal.IsPrime.ne_top inferInstance)
      (Ideal.eq_top_of_isUnit_mem s hx
      (IsLocalization.map_units T (⟨x, h⟩ : Q.primeCompl)))
  let : Algebra R B := f.toAlgebra
  let g : P.ResidueField →ₐ[R] r.ResidueField :=
    Ideal.ResidueField.mapₐ P r (Algebra.ofId R B) hc
  have hg : Function.Bijective g :=
    (RingHom.surjectiveOnStalks_of_surjective hf).residueFieldMap_bijective P r hc
  let η : P.ResidueField ≃ₐ[R] s.ResidueField :=
    AlgEquiv.ofBijective (Ideal.ResidueField.mapₐ P s (Algebra.ofId R T) rfl)
      (RingHom.SurjectiveOnStalks.residueFieldMap_bijective
        (RingHom.surjectiveOnStalks_of_isLocalization (M := Q.primeCompl) T) P s rfl)
  let σR : r.ResidueField ≃ₐ[R] s.ResidueField := (AlgEquiv.ofBijective g hg).symm.trans η
  let σ := σR.toRingEquiv
  obtain ⟨eC⟩ := AdicCompletion.nonempty_surjective_baseChange R B hf Q q hQ
  let e1 : r.Fiber Cq ≃ₐ[r.ResidueField] TensorProduct R r.ResidueField Cp :=
    (Algebra.TensorProduct.congr (AlgEquiv.refl : r.ResidueField ≃ₐ[r.ResidueField]
      r.ResidueField) eC).trans
      (Algebra.TensorProduct.cancelBaseChange R B r.ResidueField r.ResidueField Cp)
  let : Algebra r.ResidueField s.ResidueField := σ.toRingHom.toAlgebra
  let : IsScalarTower R r.ResidueField s.ResidueField :=
    .of_algebraMap_eq' (RingHom.ext (fun x ↦ (σR.commutes x).symm))
  let σA : r.ResidueField ≃ₐ[r.ResidueField] s.ResidueField :=
    { σ with commutes' := fun _ ↦ rfl }
  let e2 : TensorProduct R r.ResidueField Cp ≃ₐ[r.ResidueField]
      TensorProduct R s.ResidueField Cp :=
    Algebra.TensorProduct.congr σA (AlgEquiv.refl : Cp ≃ₐ[R] Cp)
  let : TensorProduct.CompatibleSMul R T s.ResidueField Cp :=
    IsLocalization.tensorProduct_compatibleSMul Q.primeCompl T s.ResidueField Cp
  let e3 : s.Fiber Cp ≃ₐ[r.ResidueField] TensorProduct R s.ResidueField Cp :=
    Algebra.TensorProduct.equivOfCompatibleSMul R T r.ResidueField s.ResidueField Cp
  let e := e1.trans (e2.trans e3.symm)
  refine ⟨σ, e.toRingEquiv, ?_⟩
  intro x a
  exact e.toLinearEquiv.map_smul x a

end Polynomial
