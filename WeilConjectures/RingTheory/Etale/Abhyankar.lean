/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.RingTheory.Etale.Abhyankar.Galois
public import WeilConjectures.RingTheory.Etale.Abhyankar.Product
public import Mathlib.RingTheory.Invariant.Galois
public import Mathlib.RingTheory.Artinian.Module

/-!
# Abhyankar's lemma for Galois algebras over a discrete valuation ring

Let `O` be a discrete valuation ring with uniformizer `π` and fraction field `F`, and let `L` be
a finite étale `F`-algebra with an action of a finite group `G` by `F`-algebra automorphisms
such that `L` is Galois with group `G` (`[L : F] = |G|` and `L^G = F`). Assume `|G|` divides an
integer `n` invertible in `O`. Then the extension is tamely ramified, and after adjoining an
`n`-th root `t` of `π` it becomes unramified: the integral closure of `O₂ = O[t]/(tⁿ - π)` in
`O₂ ⊗_O L` is finite étale over `O₂` (here `O₂` is any `O`-algebra presented as `O[X]/(Xⁿ - π)`)
(`IsDiscreteValuationRing.etale_integralClosure_adjoinRoot`).

This is Abhyankar's lemma ([Stacks 0EYG], [Stacks 09E8] for the tameness), an input of the trait
case of blueprint `sbc-thm-spreading-finite-etale-galois` ([Stacks 0EYJ]).

The étale algebra `L` is the product of the fields `L ⧸ M`, `M` maximal, each of which is a
Galois extension of `F` of degree dividing `|G|`
(`Algebra.IsInvariant.isGalois_quotient_and_finrank_dvd`). We conclude by the case of a Galois
field extension (`IsDiscreteValuationRing.etale_integralClosure_adjoinRoot_of_isGalois`), since
the conclusion is compatible with finite products.
-/

@[expose] public section

universe u

open Polynomial TensorProduct

attribute [local instance] Ideal.Quotient.field

/-- Let `L` be an étale algebra over a field `F` with an action of a finite group `G` by
`F`-algebra automorphisms, such that `L^G = F`. Then for every maximal ideal `M` of `L`, the
field `L ⧸ M` is a Galois extension of `F` whose degree divides `|G|`. -/
theorem Algebra.IsInvariant.isGalois_quotient_and_finrank_dvd {F L : Type*} [Field F]
    [CommRing L] [Algebra F L] [Algebra.Etale F L] (G : Type*) [Group G] [Finite G]
    [MulSemiringAction G L] [SMulCommClass G F L] [Algebra.IsInvariant F L G] (M : Ideal L)
    [M.IsMaximal] : IsGalois F (L ⧸ M) ∧ Module.finrank F (L ⧸ M) ∣ Nat.card G := by
  have : Module.Finite F L := Algebra.FormallyUnramified.finite_of_free F L
  have : Module.Finite F (L ⧸ M) :=
    .of_surjective (Ideal.Quotient.mkₐ F M).toLinearMap Ideal.Quotient.mk_surjective
  let _ : Algebra (F ⧸ (⊥ : Ideal F)) F := (RingEquiv.quotientBot F).toRingHom.toAlgebra
  have : IsFractionRing (F ⧸ (⊥ : Ideal F)) F := IsLocalization.isLocalization_of_algEquiv _
    (AlgEquiv.ofRingEquiv (f := RingEquiv.quotientBot F) fun _ ↦ rfl)
  have : M.LiesOver (⊥ : Ideal F) := ⟨(Ideal.eq_bot_of_prime _).symm⟩
  have : IsScalarTower (F ⧸ (⊥ : Ideal F)) F (L ⧸ M) := .of_algebraMap_eq fun x ↦ by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rfl
  have : Normal F (L ⧸ M) := Ideal.IsFractionRing.normal G (⊥ : Ideal F) M F (L ⧸ M)
  have : Algebra.IsSeparable F (L ⧸ M) := Algebra.FormallyUnramified.isSeparable F (L ⧸ M)
  have : IsGalois F (L ⧸ M) := isGalois_iff.mpr ⟨inferInstance, inferInstance⟩
  refine ⟨this, ?_⟩
  rw [← IsGalois.card_aut_eq_finrank]
  exact (Subgroup.card_dvd_of_surjective _
    (IsFractionRing.stabilizerHom_surjective G (⊥ : Ideal F) M F (L ⧸ M))).trans
    (Subgroup.card_subgroup_dvd_card _)

namespace IsDiscreteValuationRing

variable {O F L : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field F]
  [Algebra O F] [IsFractionRing O F] [CommRing L] [Algebra F L] [Algebra O L]
  [IsScalarTower O F L] [Algebra.Etale F L]

/-- **Abhyankar's lemma** for Galois algebras over a discrete valuation ring. See the module
docstring. -/
theorem etale_integralClosure_adjoinRoot (G : Type*) [Group G] [Finite G]
    [MulSemiringAction G L] [SMulCommClass G F L]
    (_hrank : Module.finrank F L = Nat.card G)
    (hfix : ∀ x : L, (∀ g : G, g • x = x) → x ∈ Set.range (algebraMap F L))
    {n : ℕ} (hGn : Nat.card G ∣ n) (hn : IsUnit (n : O)) {π : O} (hπ : Irreducible π)
    (O₂ : Type u) [CommRing O₂] [Algebra O O₂] (hO₂ : IsAdjoinRoot O₂ (X ^ n - C π)) :
    Algebra.Etale O₂ (integralClosure O₂ (O₂ ⊗[O] L)) ∧
      Module.Finite O₂ (integralClosure O₂ (O₂ ⊗[O] L)) := by
  have : Algebra.IsInvariant F L G := ⟨hfix⟩
  have : IsReduced L := Algebra.FormallyUnramified.isReduced_of_field F L
  have : Module.Finite F L := Algebra.FormallyUnramified.finite_of_free F L
  have : IsArtinianRing L := isArtinian_of_tower F inferInstance
  let e : L ≃ₐ[O] Π I : MaximalSpectrum L, L ⧸ I.asIdeal :=
    ((IsArtinianRing.equivPi L).restrictScalars F).restrictScalars O
  refine etale_integralClosure_tensorProduct_of_algEquiv e.symm
    (etale_integralClosure_tensorProduct_pi _ fun I ↦ ?_)
  obtain ⟨_, hdeg⟩ := Algebra.IsInvariant.isGalois_quotient_and_finrank_dvd (F := F) G I.asIdeal
  exact etale_integralClosure_adjoinRoot_of_isGalois (hdeg.trans hGn) hn hπ O₂ hO₂

end IsDiscreteValuationRing
