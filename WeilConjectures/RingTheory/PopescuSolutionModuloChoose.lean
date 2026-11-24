/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.GRing
public import WeilConjectures.RingTheory.PopescuAdmissibleSubalgebra
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.LinearAlgebra.Basis.Defs
import WeilConjectures.RingTheory.PopescuQuotientBasisEnlargement
import Mathlib.RingTheory.LocalRing.Module

/-!
# Choosing elements in an admissible Popescu subalgebra

Given a Popescu-admissible subalgebra `A₀` of `Λ_q / (q Λ_q)^n`, we enlarge it to an admissible
`A` containing images of elements of `Λ` whose residues have differentials forming a basis of
`Ω_{F/k}` (with `F` the residue field of `A`), and images of elements of `q` generating `q Λ_q`.

## Implementation details

The enlargement itself is `exists_popescu_admissible_quotient_basis`. Here we construct the
embedding of the residue field of `A` into `κ(q)` and upgrade generation modulo `(q Λ_q)^n` to
generation of `q Λ_q`: for `n = 1` we take generators of `q`, and for `n ≥ 2` we use Nakayama's
lemma.

## References

* Stacks Project, proofs of Tags 07FH and 07FI
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace Algebra

/-- Given a Popescu-admissible `A₀ ⊆ Λ_q / (q Λ_q)^n`, there is an admissible local
`A ⊇ A₀` whose maximal ideal is the preimage of the image of `q Λ_q`, together with an
injective `k`-embedding of its residue field `F` into `κ(q)` compatible with the quotient maps,
elements `xs` of `Λ` mapping into `A` whose residues have differentials forming a basis of
`Ω_{F/k}`, and elements `ys` of `q` mapping into `A` that generate `q Λ_q`. -/
theorem exists_popescu_admissible_differential_basis
    (k : Type u) (Λ : Type v) [Field k] [CommRing Λ] [Algebra k Λ]
    [IsNoetherianRing Λ] (p : ℕ) [CharP k p] (hp : 0 < p)
    (hreg : IsGeometricallyRegular k Λ) (q : Ideal Λ) [q.IsPrime]
    (n : ℕ) (hn : 1 ≤ n)
    (A₀ : Subalgebra k (Localization.AtPrime q ⧸
      (q.map (algebraMap Λ (Localization.AtPrime q))) ^ n))
    (hA₀ : A₀.IsPopescuAdmissible ((q.map (algebraMap Λ (Localization.AtPrime q))).map
      (Ideal.Quotient.mk ((q.map (algebraMap Λ (Localization.AtPrime q))) ^ n)))) :
    ∃ (A : Subalgebra k (Localization.AtPrime q ⧸
        (q.map (algebraMap Λ (Localization.AtPrime q))) ^ n)) (_ : IsLocalRing A),
      A₀ ≤ A ∧
      A.IsPopescuAdmissible ((q.map (algebraMap Λ (Localization.AtPrime q))).map
        (Ideal.Quotient.mk ((q.map (algebraMap Λ (Localization.AtPrime q))) ^ n))) ∧
      IsLocalRing.maximalIdeal A = Ideal.comap A.val.toRingHom
        ((q.map (algebraMap Λ (Localization.AtPrime q))).map
          (Ideal.Quotient.mk ((q.map (algebraMap Λ (Localization.AtPrime q))) ^ n))) ∧
      ∃ (ι : IsLocalRing.ResidueField A →ₐ[k] q.ResidueField),
        Function.Injective ι ∧
        (∀ (a : A) (x : Localization.AtPrime q),
          (a : Localization.AtPrime q ⧸
            (q.map (algebraMap Λ (Localization.AtPrime q))) ^ n) =
            Ideal.Quotient.mk ((q.map (algebraMap Λ (Localization.AtPrime q))) ^ n) x →
          ι (IsLocalRing.residue A a) = IsLocalRing.residue (Localization.AtPrime q) x) ∧
        ∃ (t r : ℕ) (xs : Fin t → Λ) (ys : Fin r → Λ)
          (a : Fin t → A) (a' : Fin r → A),
          (∀ j, (a j : Localization.AtPrime q ⧸
            (q.map (algebraMap Λ (Localization.AtPrime q))) ^ n) =
            Ideal.Quotient.mk ((q.map (algebraMap Λ (Localization.AtPrime q))) ^ n)
              (algebraMap Λ (Localization.AtPrime q) (xs j))) ∧
          (∀ i, ys i ∈ q ∧ (a' i : Localization.AtPrime q ⧸
            (q.map (algebraMap Λ (Localization.AtPrime q))) ^ n) =
            Ideal.Quotient.mk ((q.map (algebraMap Λ (Localization.AtPrime q))) ^ n)
              (algebraMap Λ (Localization.AtPrime q) (ys i))) ∧
          (∃ b : Module.Basis (Fin t) (IsLocalRing.ResidueField A)
              (KaehlerDifferential k (IsLocalRing.ResidueField A)),
            ∀ j, b j = KaehlerDifferential.D k (IsLocalRing.ResidueField A)
              (IsLocalRing.residue A (a j))) ∧
          Ideal.span (Set.range (fun i => algebraMap Λ (Localization.AtPrime q) (ys i))) =
            q.map (algebraMap Λ (Localization.AtPrime q)) := by
  classical
  let L := Localization.AtPrime q
  let m : Ideal L := q.map (algebraMap Λ L)
  let B := L ⧸ m ^ n
  let π : L →+* B := Ideal.Quotient.mk (m ^ n)
  have hm : m = IsLocalRing.maximalIdeal L :=
    IsLocalization.AtPrime.map_eq_maximalIdeal q L
  have hpow : m ^ n ≤ m := Ideal.pow_le_self (by omega)
  let f : B →ₐ[k] q.ResidueField := Ideal.Quotient.liftₐ (m ^ n)
    (IsScalarTower.toAlgHom k L q.ResidueField) (fun x hx ↦ by
      change IsLocalRing.residue L x = 0
      exact (IsLocalRing.residue_eq_zero_iff x).mpr (hm ▸ hpow hx))
  have hf : RingHom.ker f.toRingHom = m.map π := by
    dsimp only [f, Ideal.Quotient.liftₐ]
    rw [Ideal.ker_quotient_lift]
    change (RingHom.ker (IsLocalRing.residue L)).map π = m.map π
    rw [IsLocalRing.ker_residue, ← hm]
  obtain ⟨A, hlocal, hle, hAdm, t, r, xs, ys, a, a', ha, ha', hb, hspan⟩ :=
    exists_popescu_admissible_quotient_basis k Λ p hp hreg q n hn A₀ hA₀
  let : IsLocalRing A := hlocal
  have hmap : (IsLocalRing.maximalIdeal A).map A.val.toRingHom = m.map π := by
    obtain ⟨_, _, hlocal', _, hmap⟩ := hAdm
    exact hmap
  have hmax : IsLocalRing.maximalIdeal A = Ideal.comap A.val.toRingHom (m.map π) := by
    apply Ideal.IsMaximal.eq_of_le (IsLocalRing.maximalIdeal.isMaximal A)
    · rw [← hf, RingHom.comap_ker]
      exact RingHom.ker_ne_top (f.toRingHom.comp A.val.toRingHom)
    · rw [← hmap]
      exact Ideal.le_comap_map
  let ι : IsLocalRing.ResidueField A →ₐ[k] q.ResidueField :=
    Ideal.Quotient.liftₐ (IsLocalRing.maximalIdeal A) (f.comp A.val) (fun x hx ↦ by
      apply RingHom.mem_ker.mp
      change (x : B) ∈ RingHom.ker f.toRingHom
      rw [hf]
      change x ∈ Ideal.comap A.val.toRingHom (m.map π)
      rwa [← hmax])
  refine ⟨A, hlocal, hle, hAdm, hmax, ι, ι.injective, ?_, ?_⟩
  · intro z x hz
    change f (z : B) = IsLocalRing.residue L x
    rw [hz]
    rfl
  · by_cases hn1 : n = 1
    · obtain ⟨r', zs, hzs⟩ :=
        Submodule.fg_iff_exists_fin_generating_family.mp (IsNoetherian.noetherian q)
      have hzmem : ∀ i, zs i ∈ q := fun i ↦ hzs ▸ Ideal.subset_span ⟨i, rfl⟩
      have hzero : ∀ i, π (algebraMap Λ L (zs i)) = 0 := by
        intro i
        apply Ideal.Quotient.eq_zero_iff_mem.mpr
        simpa [hn1] using (Ideal.mem_map_of_mem (algebraMap Λ L) (hzmem i))
      refine ⟨t, r', xs, zs, a, fun _ ↦ 0, ha, ?_, hb, ?_⟩
      · intro i
        exact ⟨hzmem i, (hzero i).symm⟩
      · have h := congrArg (Ideal.map (algebraMap Λ L)) hzs
        rwa [Ideal.map_span, ← Set.range_comp] at h
    · have hn2 : 2 ≤ n := by omega
      have hJle : Ideal.span (Set.range (fun i ↦ algebraMap Λ L (ys i))) ≤ m := by
        apply Ideal.span_le.mpr
        rintro _ ⟨i, rfl⟩
        exact Ideal.mem_map_of_mem _ (ha' i).1
      have hJmap : (Ideal.span (Set.range (fun i ↦ algebraMap Λ L (ys i)))).map π =
          m.map π := by
        rw [Ideal.map_span, ← Set.range_comp]
        exact hspan
      have hsup : m ≤ Ideal.span (Set.range (fun i ↦ algebraMap Λ L (ys i))) ⊔ m ^ n := by
        have h := congrArg (Ideal.comap π) hJmap
        rw [Ideal.comap_map_quotientMk, Ideal.comap_map_mk hpow] at h
        exact le_of_eq (h.symm.trans (sup_comm _ _))
      have hJ : Ideal.span (Set.range (fun i ↦ algebraMap Λ L (ys i))) = m := by
        apply le_antisymm hJle
        apply Submodule.le_of_le_smul_of_le_jacobson_bot (I := m)
          (IsNoetherian.noetherian m)
        · rw [IsLocalRing.jacobson_eq_maximalIdeal (⊥ : Ideal L) bot_ne_top, ← hm]
        · exact hsup.trans (sup_le_sup_left
            (by simpa [Ideal.smul_eq_mul, pow_two] using
              (Ideal.pow_le_pow_right (I := m) hn2)) _)
      exact ⟨t, r, xs, ys, a, a', ha, ha', hb, hJ⟩

end Algebra
