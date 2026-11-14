/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Extension.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Operations
import WeilConjectures.AlgebraicGeometry.ArtinianLiftingFiniteKernel
import Mathlib.RingTheory.Ideal.Quotient.Noetherian
import Mathlib.RingTheory.HopkinsLevitzki
import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-! # Truncated Artinian sections

## References

* Stacks Project, Tag 02HT
-/

@[expose] public section

universe u v

namespace Algebra

/-- The length-one Artinian lifting tests produce sections at every positive truncation:
the quotient map `P.Ring / (J ^ 2 + m ^ N) → P.Ring / (J + m ^ N)` has an `R`-algebra section
(Stacks, Tag 02HT). -/
theorem artinian_lifting_truncated_section
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    (q : Ideal A) [q.IsPrime]
    (P : Extension.{u} R (Localization.AtPrime q))
    [IsLocalRing P.Ring] [IsNoetherianRing P.Ring]
    (hlift : ∀ (B' B : Type (max u v)) [CommRing B'] [CommRing B]
      [IsArtinianRing B'] [IsArtinianRing B] [IsLocalRing B'] [IsLocalRing B]
      (φ : B' →+* B), Function.Surjective φ → Module.length B' (RingHom.ker φ) = 1 →
      ∀ (ρ : R →+* B') (a : A →+* B),
        a.comp (algebraMap R A) = φ.comp ρ →
          Ideal.comap a (IsLocalRing.maximalIdeal B) = q →
        ∃ a' : A →+* B', φ.comp a' = a ∧ a'.comp (algebraMap R A) = ρ) :
    ∀ (N : ℕ), 1 ≤ N →
      ∃ σ : (P.Ring ⧸ (P.ker ⊔ IsLocalRing.maximalIdeal P.Ring ^ N)) →ₐ[R]
          (P.Ring ⧸ (P.ker ^ 2 ⊔ IsLocalRing.maximalIdeal P.Ring ^ N)),
        (Ideal.Quotient.factorₐ R
          (sup_le_sup (Ideal.pow_le_self (by decide : 2 ≠ 0)) le_rfl)).comp σ =
            AlgHom.id R _ := by
  intro N hN
  let C := P.Ring
  let S := Localization.AtPrime q
  let m := IsLocalRing.maximalIdeal C
  let I : Ideal C := P.ker ^ 2 ⊔ m ^ N
  let L : Ideal C := P.ker ⊔ m ^ N
  let f : C →ₐ[R] S := IsScalarTower.toAlgHom R C S
  have hf : Function.Surjective f := P.algebraMap_surjective
  have hfLocal : IsLocalHom f.toRingHom := IsLocalHom.of_surjective _ hf
  have hJ : P.ker ≤ m := by
    intro x hx
    have hz : f x = 0 := hx
    change x ∈ IsLocalRing.maximalIdeal C
    rw [← IsLocalRing.maximalIdeal_comap f.toRingHom]
    change f x ∈ IsLocalRing.maximalIdeal S
    rw [hz]
    exact Ideal.zero_mem _
  have hIm : I ≤ m := sup_le
    ((Ideal.pow_le_self (by decide : 2 ≠ 0)).trans hJ)
    (Ideal.pow_le_self (by omega))
  have hLm : L ≤ m := sup_le hJ (Ideal.pow_le_self (by omega))
  have hI : I ≠ ⊤ := ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal C).ne_top hIm
  have hL : L ≠ ⊤ := ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal C).ne_top hLm
  have : Nontrivial (C ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
  have : Nontrivial (C ⧸ L) := Ideal.Quotient.nontrivial_iff.mpr hL
  have : IsLocalRing (C ⧸ I) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  have : IsLocalRing (C ⧸ L) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk L) Ideal.Quotient.mk_surjective
  have hnil : IsLocalRing.maximalIdeal (C ⧸ I) ^ N = ⊥ := by
    rw [← IsLocalRing.map_maximalIdeal_of_surjective (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective, ← Ideal.map_pow]
    exact (Ideal.map_eq_bot_iff_le_ker _).mpr (by rw [Ideal.mk_ker]; exact le_sup_right)
  have hnilL : IsLocalRing.maximalIdeal (C ⧸ L) ^ N = ⊥ := by
    rw [← IsLocalRing.map_maximalIdeal_of_surjective (Ideal.Quotient.mk L)
      Ideal.Quotient.mk_surjective, ← Ideal.map_pow]
    exact (Ideal.map_eq_bot_iff_le_ker _).mpr (by rw [Ideal.mk_ker]; exact le_sup_right)
  have : IsArtinianRing (C ⧸ I) :=
    (isArtinianRing_iff_isNilpotent_maximalIdeal _).mpr ⟨N, hnil⟩
  have : IsArtinianRing (C ⧸ L) :=
    (isArtinianRing_iff_isNilpotent_maximalIdeal _).mpr ⟨N, hnilL⟩
  let t : S →ₐ[R] (C ⧸ L) := AlgHom.liftOfSurjective f hf
    (Ideal.Quotient.mkₐ R L) (by
      change P.ker ≤ RingHom.ker (Ideal.Quotient.mk L)
      rw [Ideal.mk_ker]
      exact le_sup_left)
  have ht (x : C) : t (f x) = Ideal.Quotient.mk L x :=
    AlgHom.liftOfSurjective_apply _ _ _ _ x
  have htSurj : Function.Surjective t := by
    intro y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact ⟨f x, ht x⟩
  have htLocal : IsLocalHom t.toRingHom := IsLocalHom.of_surjective _ htSurj
  let φ : (C ⧸ I) →ₐ[R] (C ⧸ L) := Ideal.Quotient.factorₐ R
    (sup_le_sup (Ideal.pow_le_self (by decide : 2 ≠ 0)) le_rfl)
  have hφSurj : Function.Surjective φ := Ideal.Quotient.factor_surjective
    (sup_le_sup (Ideal.pow_le_self (by decide : 2 ≠ 0)) le_rfl)
  have hφLocal : IsLocalHom φ.toRingHom := IsLocalHom.of_surjective _ hφSurj
  let a : A →+* (C ⧸ L) := t.toRingHom.comp (algebraMap A S)
  have ha : a.comp (algebraMap R A) = φ.toRingHom.comp (algebraMap R (C ⧸ I)) := by
    ext r
    change t ((algebraMap A S) ((algebraMap R A) r)) =
      φ ((algebraMap R (C ⧸ I)) r)
    rw [← IsScalarTower.algebraMap_apply R A S, t.commutes, φ.commutes]
  have haq : Ideal.comap a (IsLocalRing.maximalIdeal (C ⧸ L)) = q := by
    dsimp only [a]
    rw [← Ideal.comap_comap, IsLocalRing.maximalIdeal_comap]
    exact IsLocalization.AtPrime.under_maximalIdeal S q
  obtain ⟨a', ha', hR⟩ := artinian_lifting_finite_kernel.{u, v} q hlift
    (C ⧸ I) (C ⧸ L) φ.toRingHom hφSurj (algebraMap R (C ⧸ I)) a ha haq
  have ha'q : Ideal.comap a' (IsLocalRing.maximalIdeal (C ⧸ I)) = q := by
    rw [← IsLocalRing.maximalIdeal_comap φ.toRingHom, Ideal.comap_comap, ha']
    exact haq
  have hu (y : q.primeCompl) : IsUnit (a' y) := by
    apply IsLocalRing.notMem_maximalIdeal.mp
    change y.1 ∉ Ideal.comap a' (IsLocalRing.maximalIdeal (C ⧸ I))
    rw [ha'q]
    exact y.2
  let b : S →+* (C ⧸ I) := IsLocalization.lift hu
  have hb : b.comp (algebraMap A S) = a' := IsLocalization.lift_comp hu
  have hbt : φ.toRingHom.comp b = t.toRingHom := by
    apply IsLocalization.ringHom_ext q.primeCompl
    rw [RingHom.comp_assoc, hb, ha']
  have hbLocal : IsLocalHom b := by
    have : IsLocalHom (φ.toRingHom.comp b) := hbt ▸ htLocal
    exact isLocalHom_of_comp b φ.toRingHom
  let bₐ : S →ₐ[R] (C ⧸ I) :=
    { toRingHom := b
      commutes' := by
        intro r
        change b ((algebraMap R S) r) = _
        rw [IsScalarTower.algebraMap_apply R A S]
        rw [show b ((algebraMap A S) ((algebraMap R A) r)) =
          a' ((algebraMap R A) r) from DFunLike.congr_fun hb ((algebraMap R A) r)]
        exact DFunLike.congr_fun hR r }
  let g : C →ₐ[R] (C ⧸ I) := bₐ.comp f
  have hgLocal : IsLocalHom g.toRingHom :=
    inferInstanceAs (IsLocalHom (b.comp f.toRingHom))
  have hm : m.map g.toRingHom ≤ IsLocalRing.maximalIdeal (C ⧸ I) :=
    IsLocalRing.map_maximalIdeal_le g.toRingHom
  have hpow : m ^ N ≤ RingHom.ker g.toRingHom := by
    apply (Ideal.map_eq_bot_iff_le_ker _).mp
    apply le_bot_iff.mp
    rw [Ideal.map_pow]
    exact (pow_le_pow_left' hm N).trans hnil.le
  have hker : L ≤ RingHom.ker g.toRingHom := by
    apply sup_le _ hpow
    intro x hx
    change b (f x) = 0
    rw [show f x = 0 from hx, map_zero]
  let σ : (C ⧸ L) →ₐ[R] (C ⧸ I) := Ideal.Quotient.liftₐ L g hker
  refine ⟨σ, ?_⟩
  apply AlgHom.ext
  intro y
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
  change φ (g x) = Ideal.Quotient.mk L x
  change φ (b (f x)) = _
  exact (DFunLike.congr_fun hbt (f x)).trans (ht x)

end Algebra
