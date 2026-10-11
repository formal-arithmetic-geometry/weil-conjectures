/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.BaseChangeProperty

/-!
# Change of coefficients for the base change property

Let `Λ` be a commutative ring and `N` a positive integer, and put `Λ_N = Λ ⧸ NΛ`. Restriction of
scalars along `Λ ⟶ Λ_N` is exact and conservative, commutes with `g^*` and `f_*`, and commutes
with `Rf_*`: an injective sheaf of `Λ_N`-modules has no higher cohomology as a sheaf of
`Λ`-modules. It therefore carries the derived base change map over `Λ_N` to the one over `Λ`.

Consequently:

- the base change property with `Λ`-coefficients implies the one with `Λ_N`-coefficients
  (`AlgebraicGeometry.Etale.HasTorsionBaseChange.quotient`), since a complex of sheaves of
  `Λ_N`-modules has torsion cohomology as a complex of sheaves of `Λ`-modules;
- for a quasi-compact quasi-separated `f`, the base change property with `Λ_p`-coefficients for
  every prime `p` implies the one with `Λ`-coefficients
  (`AlgebraicGeometry.Etale.hasTorsionBaseChange_of_forall_prime`): by truncation an object of
  `D⁺` with torsion cohomology is reduced to a torsion sheaf in one degree, a torsion sheaf is a
  filtered colimit of sheaves killed by integers, which are successive extensions of sheaves
  killed by primes (`AlgebraicGeometry.Etale.isIso_baseChangeHomologyMap_of_isTorsionSheaf`),
  and a sheaf of `Λ`-modules killed by `p` is a sheaf of `Λ_p`-modules.

This is the change of coefficients in the proof of the reduction of proper base change to the
projective line (blueprint `sk-thm-reduction`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme Etale

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- **Base change property for a quotient coefficient ring.** If `f` satisfies the base change
property with `Λ`-coefficients, then also with `Λ ⧸ NΛ`-coefficients: restriction of scalars
along `Λ ⟶ Λ ⧸ NΛ` is conservative, sends complexes of `Λ ⧸ NΛ`-modules to complexes with
torsion cohomology, and carries the derived base change map over `Λ ⧸ NΛ` to the one over `Λ`.
(blueprint: `sk-thm-reduction`, change of coefficients) -/
theorem Etale.HasTorsionBaseChange.quotient {X Y : Scheme.{u}} {f : X ⟶ Y}
    (hf : Etale.HasTorsionBaseChange Λ f) (N : ℕ) :
    Etale.HasTorsionBaseChange (Λ ⧸ Ideal.span {(N : Λ)}) f :=
  sorry

/-- **Base change property from prime coefficient rings.** Let `f` be quasi-compact and
quasi-separated. If `f` satisfies the base change property with `Λ ⧸ pΛ`-coefficients for every
prime `p`, then also with `Λ`-coefficients.
(blueprint: `sk-thm-reduction`, change of coefficients;
`lemma-weil-pbc-property-iff-acyclicity`, from prime to arbitrary torsion) -/
theorem Etale.hasTorsionBaseChange_of_forall_prime {X Y : Scheme.{u}} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f]
    (h : ∀ p : ℕ, p.Prime → Etale.HasTorsionBaseChange (Λ ⧸ Ideal.span {(p : Λ)}) f) :
    Etale.HasTorsionBaseChange Λ f :=
  sorry

/-- The quotient `Λ ⧸ NΛ` of a ring by a positive integer is torsion as an additive group: it is
killed by `N`. -/
lemma isAddTorsion_quotient_span_natCast {N : ℕ} (hN : 0 < N) :
    IsAddTorsion (Λ ⧸ Ideal.span {(N : Λ)}) := fun x ↦
  (isOfFinAddOrder_iff_nsmul_eq_zero).2 ⟨N, hN, by
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [nsmul_eq_mul, ← map_natCast (Ideal.Quotient.mk _), ← map_mul,
      Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)⟩

/-- **Injective acyclicity implies the base change property.** If a proper morphism
`f : X ⟶ Y` has injective acyclicity with `Λ ⧸ pΛ`-coefficients for every prime `p`, then it
satisfies the base change property with `Λ`-coefficients: for the torsion rings `Λ ⧸ pΛ` this is
`AlgebraicGeometry.Etale.hasTorsionBaseChange_iff_hasInjectiveAcyclicity`, and the passage to `Λ`
is `AlgebraicGeometry.Etale.hasTorsionBaseChange_of_forall_prime`.
(blueprint: `lemma-weil-pbc-property-iff-acyclicity`, `IA_r(f)` for every prime `r` implies
`PBC(f)`) -/
@[stacks 0A4B]
theorem Etale.hasTorsionBaseChange_of_hasInjectiveAcyclicity {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsProper f]
    (hf : ∀ p : ℕ, p.Prime → Etale.HasInjectiveAcyclicity (Λ ⧸ Ideal.span {(p : Λ)}) f) :
    Etale.HasTorsionBaseChange Λ f :=
  Etale.hasTorsionBaseChange_of_forall_prime Λ f fun p hp ↦
    (Etale.hasTorsionBaseChange_iff_hasInjectiveAcyclicity _
      (isAddTorsion_quotient_span_natCast Λ hp.pos) f).2 (hf p hp)

end AlgebraicGeometry
