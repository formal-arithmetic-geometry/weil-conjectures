/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.RingTheory.SingularIdeal
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.LinearAlgebra.Basis.Defs
import WeilConjectures.RingTheory.SmoothLocalizationConormalSplit
import WeilConjectures.RingTheory.SelectedBasisOfLocalizedSplit
import Mathlib.RingTheory.Smooth.Locus

/-!
# Conormal data at a smooth point

For a polynomial quotient that is smooth at a prime, we produce a smooth principal localization
around the prime on which the localized conormal module is free, with a basis given by the
classes of some of the given generators.

## References

* [Stacks, Tag 07C6]
-/

@[expose] public section
universe u
namespace Algebra
/-- If `C = R[x₁, ..., xₙ]/(f₁, ..., f_m)` is smooth over `R` at a prime `q`, there is an `a`
outside `q` with `C_a` smooth over `R` and a subset of `c ≤ min n m` of the generators `f_j` whose
classes form a basis of the localized conormal module `(I/I²)_a`. -/
theorem exists_smoothAtPrime_conormal_data
    (R : Type u) [CommRing R] (n m : ℕ)
    (f : Fin m → MvPolynomial (Fin n) R)
    (q : PrimeSpectrum (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f)))
    (hs : Algebra.IsSmoothAtPrime R q) :
    ∃ (a : MvPolynomial (Fin n) R),
      Ideal.Quotient.mk (Ideal.span (Set.range f)) a ∉ q.asIdeal ∧
      ∃ (V : Finset (Fin m)) (c : ℕ),
        V.card = c ∧ c ≤ min n m ∧
        Algebra.Smooth R (Localization.Away
          (Ideal.Quotient.mk (Ideal.span (Set.range f)) a)) ∧
        (∃ (e : Fin c ≃ V),
          ∃ b : Module.Basis (Fin c)
              (Localization.Away
                (Ideal.Quotient.mk (Ideal.span (Set.range f)) a))
              (LocalizedModule.Away
                (Ideal.Quotient.mk (Ideal.span (Set.range f)) a)
                (Ideal.span (Set.range f)).Cotangent),
            ∀ j : Fin c,
              b j = LocalizedModule.mkLinearMap
                (Submonoid.powers
                  (Ideal.Quotient.mk (Ideal.span (Set.range f)) a))
                (Ideal.span (Set.range f)).Cotangent
                ((Ideal.span (Set.range f)).toCotangent
                  ⟨f (e j).1,
                    Ideal.subset_span ⟨(e j).1, rfl⟩⟩)) := by
  classical
  let P := MvPolynomial (Fin n) R
  let I : Ideal P := Ideal.span (Set.range f)
  let A := P ⧸ I
  let v : Fin m → I := fun i ↦ ⟨f i, Ideal.subset_span ⟨i, rfl⟩⟩
  let x : Fin m → I.Cotangent := fun i ↦ I.toCotangent (v i)
  have hv : Submodule.span P (Set.range v) = ⊤ :=
    (Submodule.span_range_subtype_eq_top_iff I (fun i ↦ (v i).2)).mpr rfl
  have hxP : Submodule.span P (Set.range x) = ⊤ := by
    change Submodule.span P (Set.range (I.toCotangent ∘ v)) = ⊤
    rw [Set.range_comp, ← Submodule.map_span, hv, Submodule.map_top, I.toCotangent_range]
  have hx : Submodule.span A (Set.range x) = ⊤ := by
    apply Submodule.restrictScalars_injective P
    rw [Submodule.restrictScalars_span P A Ideal.Quotient.mk_surjective,
      Submodule.restrictScalars_top]
    exact hxP
  obtain ⟨b, hb, hsm⟩ := hs
  have : Smooth R (Localization.Away b) := hsm
  obtain ⟨d, π, hd, hπ, ⟨l, hld⟩, hrest⟩ :=
    smooth_localization_conormal_split R n I b
  obtain ⟨t, ht, V, c, hcard, hbound, e, bs, hbs⟩ :=
    Module.exists_selected_basis_away_mul_of_split n m x hx q.asIdeal b hb d l hld
  have hbt : b * t ∉ q.asIdeal := q.asIdeal.primeCompl.mul_mem hb ht
  have : Algebra.FinitePresentation R A :=
    Algebra.FinitePresentation.quotient (Submodule.fg_span (Set.finite_range f))
  have hsm' : Smooth R (Localization.Away (b * t)) := by
    apply basicOpen_subset_smoothLocus_iff_smooth.mp
    intro z hz
    exact basicOpen_subset_smoothLocus_iff_smooth.mpr hsm
      (PrimeSpectrum.basicOpen_mul_le_left b t hz)
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (b * t)
  refine ⟨a, ?_, V, c, hcard, hbound, ?_, ?_⟩
  · rwa [ha]
  · change Smooth R (Localization.Away (Ideal.Quotient.mk I a))
    rw [ha]
    exact hsm'
  · change ∃ e : Fin c ≃ V,
      ∃ bs : Module.Basis (Fin c) (Localization.Away (Ideal.Quotient.mk I a))
          (LocalizedModule.Away (Ideal.Quotient.mk I a) I.Cotangent),
        ∀ j : Fin c, bs j = LocalizedModule.mkLinearMap
          (Submonoid.powers (Ideal.Quotient.mk I a)) I.Cotangent (x (e j).1)
    rw [ha]
    exact ⟨e, bs, hbs⟩
end Algebra
