/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.IsStrictHenselization
public import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.Ideal
import WeilConjectures.RingTheory.StrictHenselizationSurjectiveQuotient

/-! # Divisor quotients of algebraic strict henselizations of prime localizations

Let `C` be a strict henselization of `R_q` and `f ∈ q`. Then `C ⧸ (f)` is a strict
henselization of `(R ⧸ (f))_p`, where `p` is the image of `q`.

## Implementation details

With `A = R_q` and `I = fA`, the localization of a quotient gives `A ⧸ I ≅ (R ⧸ (f))_p`, and
the result follows from the compatibility of strict henselization with surjective local
quotients. This works for `f = 0` as well; no regularity, Noetherianity or nonzerodivisor
hypothesis is needed.

## References

* [Stacks, Tag 05WS]
-/

@[expose] public section

universe u
namespace Algebra

/-- Quotient compatibility for an algebraic strict henselization of `R_q`, with `f ∈ q`.
Let `p` be the image of `q` in `R ⧸ (f)`, i.e. the prime with `p.comap (mk (f)) = q`
(this forces `f ∈ q`). Then `C ⧸ (b f)`, with the `(R ⧸ (f))_p`-algebra structure
induced by `b` (the hypothesis `hcomp`), is the strict henselization of `(R ⧸ (f))_p` with
respect to any separable closure `L` of its residue field. -/
theorem IsStrictHenselization.localized_divisor_quotient
    (R C : Type u) [CommRing R] [CommRing C]
    (q : Ideal R) [q.IsPrime]
    (K : Type u) [Field K]
    [Algebra (IsLocalRing.ResidueField (Localization.AtPrime q)) K]
    [IsSepClosure (IsLocalRing.ResidueField (Localization.AtPrime q)) K]
    [Algebra (Localization.AtPrime q) K]
    [IsScalarTower (Localization.AtPrime q)
      (IsLocalRing.ResidueField (Localization.AtPrime q)) K]
    [Algebra (Localization.AtPrime q) C]
    (hC : IsStrictHenselization (Localization.AtPrime q) K C)
    (b : R →+* C)
    (hbase : ∀ r : R, algebraMap (Localization.AtPrime q) C
      (algebraMap R (Localization.AtPrime q) r) = b r)
    (f : R) (p : Ideal (R ⧸ Ideal.span {f})) [p.IsPrime]
    (hp : p.comap (Ideal.Quotient.mk _) = q)
    (L : Type u) [Field L]
    [Algebra (IsLocalRing.ResidueField (Localization.AtPrime p)) L]
    [IsSepClosure (IsLocalRing.ResidueField (Localization.AtPrime p)) L]
    [Algebra (Localization.AtPrime p) L]
    [IsScalarTower (Localization.AtPrime p)
      (IsLocalRing.ResidueField (Localization.AtPrime p)) L]
    [Algebra (Localization.AtPrime p) (C ⧸ Ideal.span {b f})]
    (hcomp : ∀ r : R, algebraMap (Localization.AtPrime p) (C ⧸ Ideal.span {b f})
      (algebraMap (R ⧸ Ideal.span {f}) _ (Ideal.Quotient.mk _ r)) =
        Ideal.Quotient.mk _ (b r)) :
    IsStrictHenselization (Localization.AtPrime p) L (C ⧸ Ideal.span {b f}) := by
  classical
  let J : Ideal R := Ideal.span {f}
  let A := Localization.AtPrime q
  let I : Ideal A := J.map (algebraMap R A)
  have hmonoid : Algebra.algebraMapSubmonoid (R ⧸ J) q.primeCompl = p.primeCompl := by
    change q.primeCompl.map (Ideal.Quotient.mk J) = p.primeCompl
    have h := Ideal.map_primeCompl_comap_of_surjective
      (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective p
    subst hp
    exact h
  have hloc : IsLocalization p.primeCompl (A ⧸ I) := by
    rw [← hmonoid]
    exact inferInstance
  let e : (A ⧸ I) ≃ₐ[R ⧸ J] Localization.AtPrime p :=
    IsLocalization.algEquiv p.primeCompl (A ⧸ I) (Localization.AtPrime p)
  let π : A →+* Localization.AtPrime p := e.toRingEquiv.toRingHom.comp (Ideal.Quotient.mk I)
  have hπ : Function.Surjective π := e.surjective.comp Ideal.Quotient.mk_surjective
  have hker : RingHom.ker π = I := by
    rw [RingHom.ker_equiv_comp, Ideal.mk_ker]
  have hπr (r : R) : π (algebraMap R A r) =
      algebraMap (R ⧸ J) (Localization.AtPrime p) (Ideal.Quotient.mk J r) := by
    change e (Ideal.Quotient.mk I (algebraMap R A r)) = _
    rw [← Ideal.Quotient.algebraMap_quotient_map_quotient, e.commutes]
  have hIC : I.map (algebraMap A C) = Ideal.span {b f} := by
    simp only [I, J, Ideal.map_span, Set.image_singleton, Ideal.map_span]
    rw [hbase]
  revert hcomp
  revert ‹Algebra (Localization.AtPrime p) (C ⧸ Ideal.span {b f})›
  rw [← hIC]
  intro _ hcomp
  refine hC.surjective_quotient A K C _ L π hπ I hker ?_
  refine IsLocalization.ringHom_ext q.primeCompl (RingHom.ext fun r ↦ ?_)
  simp only [RingHom.comp_apply, hπr]
  rw [hbase]
  exact hcomp r

end Algebra
