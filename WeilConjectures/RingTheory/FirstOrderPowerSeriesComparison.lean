/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
import WeilConjectures.RingTheory.ExistsCoefficientSubring
import WeilConjectures.RingTheory.LocalFirstOrderCoordinates
import WeilConjectures.RingTheory.PowerSeriesFirstOrderCoordinates
import Mathlib.Algebra.CharP.Algebra

/-!
# A first-order power series comparison

A complete local algebra `A` over a field, with residue field `K` and `d = m.spanFinrank`,
admits a surjection onto `K[[X₁,...,X_d]] / (X₁,...,X_d)²` pulling back the maximal ideal to the
maximal ideal of `A`.

## Implementation details

A coefficient field (Tag 032A) gives a section `s : K → A` of reduction; it is a field since
the residue characteristic vanishes in the `k`-algebra `A`. Lifts `xᵢ` of a basis of `m/m²`
generate `m` by Nakayama, and every element of `A/m²` is uniquely `s(c) + Σᵢ s(cᵢ)xᵢ`. Likewise
`T/N² = K ⊕ K^d` for `T = K[[X₁,...,X_d]]`, `N = (X₁,...,X_d)`, and both decompositions have the
multiplication `(c,v)(c',v') = (cc', cv' + c'v)`, giving a ring isomorphism `A/m² ≃ T/N²`.

## References

* [Stacks, Tag 07EI]
* [Stacks, Tag 032A]
* [Stacks, Tag 0322]
-/

@[expose] public section

universe u v

namespace Algebra

private theorem exists_coefficient_field_section (k : Type u) (A : Type v)
    [Field k] [CommRing A] [Algebra k A] [IsLocalRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A] :
    ∃ s : IsLocalRing.ResidueField A →+* A,
      (IsLocalRing.residue A).comp s = RingHom.id _ := by
  let p := ringChar k
  let f := (IsLocalRing.residue A).comp (algebraMap k A)
  let : CharP (IsLocalRing.ResidueField A) p :=
    charP_of_injective_ringHom f.injective p
  obtain ⟨Λ, hΛ, _, _, hbij, hp⟩ := IsLocalRing.exists_coefficient_subring A p
  have hpA : (p : A) = 0 := by
    rw [← map_natCast (algebraMap k A), CharP.cast_eq_zero k p, map_zero]
  have hpΛ : (p : Λ) = 0 := by
    apply Subtype.val_injective
    simpa using hpA
  have hJ : (IsLocalRing.maximalIdeal A).comap Λ.subtype = ⊥ := by
    rw [hp, hpΛ, Ideal.span_singleton_zero]
  let J := (IsLocalRing.maximalIdeal A).comap Λ.subtype
  let e : (Λ ⧸ J) ≃+* IsLocalRing.ResidueField A :=
    RingEquiv.ofBijective (Ideal.quotientMap (I := J) (IsLocalRing.maximalIdeal A) Λ.subtype le_rfl)
      hbij
  let t : (Λ ⧸ J) →+* A := Ideal.Quotient.lift J Λ.subtype (by
    intro a ha
    have : a = 0 := by simpa [show J = ⊥ from hJ] using ha
    simp [this])
  have ht : (IsLocalRing.residue A).comp t = e.toRingHom := by
    ext x
    rfl
  refine ⟨t.comp e.symm.toRingHom, ?_⟩
  rw [← RingHom.comp_assoc, ht]
  ext x
  exact e.apply_symm_apply x

/-- A complete local algebra over a field has a surjective ring map to the first-order
power series quotient, taking the inverse image of the variables' ideal to its maximal
ideal. No formal smoothness of the local algebra is required.
-/
theorem exists_firstOrder_powerSeries_comparison (k : Type u) (A : Type v)
    [Field k] [CommRing A] [Algebra k A] [IsNoetherianRing A] [IsLocalRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A] :
    let T := MvPowerSeries (Fin (IsLocalRing.maximalIdeal A).spanFinrank)
      (IsLocalRing.ResidueField A)
    let N : Ideal T := Ideal.span (Set.range (fun i ↦ (MvPowerSeries.X i : T)))
    ∃ g : A →+* T ⧸ N ^ 2,
      Function.Surjective g ∧
      (N.map (Ideal.Quotient.mk (N ^ 2))).comap g =
        IsLocalRing.maximalIdeal A := by
  obtain ⟨s, hs⟩ := exists_coefficient_field_section k A
  obtain ⟨eA, heA⟩ := IsLocalRing.exists_firstOrder_coordinates A s hs
  obtain ⟨eT, heT⟩ := MvPowerSeries.exists_firstOrder_coordinates
    (Fin (IsLocalRing.maximalIdeal A).spanFinrank) (IsLocalRing.ResidueField A)
  let q := Ideal.Quotient.mk (IsLocalRing.maximalIdeal A ^ 2)
  let g := eT.symm.toRingHom.comp (eA.toRingHom.comp q)
  refine ⟨g, eT.symm.surjective.comp (eA.surjective.comp Ideal.Quotient.mk_surjective), ?_⟩
  ext a
  rw [Ideal.mem_comap, heT]
  change (eT (eT.symm (eA (q a)))).fst = 0 ↔ _
  rw [eT.apply_symm_apply, heA]
  exact IsLocalRing.residue_eq_zero_iff a

end Algebra
