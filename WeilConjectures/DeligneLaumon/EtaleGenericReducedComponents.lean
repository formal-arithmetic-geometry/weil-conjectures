/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
public import Mathlib.RingTheory.LocalProperties.Reduced
import Mathlib.RingTheory.Ideal.GoingDown
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Etale
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite

/-!
# Etale algebras over domains have finitely many reduced generic components

Source: literature/stacks-project/more-algebra.tex, Tag 0GSC, proof, reduction paragraph:
etale over a domain is reduced; the generic fibre is a finite product of fields; flat
going-down puts minimal primes over `(0)` (blueprint: lem-dl-a1-etale-generic-reduced-components).

## Main statements

* `etale_generic_reduced_components` states reducedness, finiteness of minimal primes,
  and contraction of each minimal prime to zero for an etale algebra over a domain.
-/

@[expose] public section

universe u

open CategoryTheory
namespace AlgebraicGeometry

set_option autoImplicit false
set_option linter.style.haveILetI false

/--
For a commutative integral domain `A` and a commutative `A`-algebra `C` whose affine
spectrum morphism is etale, `C` is reduced, has finitely many minimal primes, and
every minimal prime contracts to the zero ideal of `A`.

Source: literature/stacks-project/more-algebra.tex, Tag 0GSC, proof, reduction paragraph
(blueprint: lem-dl-a1-etale-generic-reduced-components).

Proof sketch: reducedness follows from the etale-over-reduced proposition applied to the
affine spectrum and the affine reducedness equivalence. Flat going-down applied to the
zero ideal and a minimal prime forces its contraction to be zero. Etaleness gives local
quasi-finiteness, and the quasi-finite algebra theorem makes the set of primes over zero
finite; the minimal primes form a subset of it.
-/
theorem etale_generic_reduced_components
    {A C : Type u} [CommRing A] [IsDomain A] [CommRing C] [Algebra A C]
    (hEtale : Etale
      (Spec.map (CommRingCat.ofHom (algebraMap A C)))) :
    _root_.IsReduced C ∧ Set.Finite (minimalPrimes C) ∧
      ∀ p : Ideal C, p ∈ minimalPrimes C →
        Ideal.comap (algebraMap A C) p = (⊥ : Ideal A) := by
  letI : Etale (Spec.map (CommRingCat.ofHom (algebraMap A C))) := hEtale
  letI : IsReduced (AlgebraicGeometry.Spec (CommRingCat.of A)) := by
    apply (affine_isReduced_iff (CommRingCat.of A)).mpr
    infer_instance
  have hredSpec : IsReduced (AlgebraicGeometry.Spec (CommRingCat.of C)) := by
    exact AlgebraicGeometry.isReduced_of_etale
      (Spec.map (CommRingCat.ofHom (algebraMap A C)))
  have hredC : _root_.IsReduced C :=
    (affine_isReduced_iff (CommRingCat.of C)).mp hredSpec
  have hflatSpec : Flat (Spec.map (CommRingCat.ofHom (algebraMap A C))) :=
    (Etale.iff_flat_and_formallyUnramified.mp hEtale).1
  have hflatRing : (algebraMap A C).Flat :=
    (Flat.SpecMap_iff.mp hflatSpec)
  have hflat : Module.Flat A C := (RingHom.flat_algebraMap_iff.mp hflatRing)
  letI : Algebra.HasGoingDown A C := by infer_instance
  have hcontract : ∀ p : Ideal C, p ∈ minimalPrimes C →
      Ideal.comap (algebraMap A C) p = (⊥ : Ideal A) := by
    intro p hp
    letI : p.IsPrime := hp.isPrime
    let q : Ideal A := Ideal.comap (algebraMap A C) p
    letI : q.IsPrime := Ideal.IsPrime.comap (algebraMap A C)
    letI : p.LiesOver q := Ideal.over_under p
    obtain ⟨p₀, hp₀p, hp₀, hp₀over⟩ :=
      Ideal.exists_ideal_le_liesOver_of_le (Q := p) (p := (⊥ : Ideal A))
        (q := q) bot_le
    have hp_le_p₀ : p ≤ p₀ := hp.2 ⟨hp₀, bot_le⟩ hp₀p
    have : p = p₀ := le_antisymm hp_le_p₀ hp₀p
    subst p₀
    exact hp₀over.over.symm
  have hq : Algebra.QuasiFinite A C := by
    have hqSpec : LocallyQuasiFinite (Spec.map (CommRingCat.ofHom (algebraMap A C))) :=
      inferInstance
    have hqRing : (algebraMap A C).QuasiFinite :=
      (HasRingHomProperty.Spec_iff (P := @LocallyQuasiFinite)).mp hqSpec
    exact (RingHom.quasiFinite_algebraMap.mp hqRing)
  letI : Algebra.QuasiFinite A C := hq
  have hfiniteOver : ((⊥ : Ideal A).primesOver C).Finite :=
    Algebra.QuasiFinite.finite_primesOver (R := A) (S := C) (⊥ : Ideal A)
  have hfinite : (minimalPrimes C).Finite := by
    apply hfiniteOver.subset
    intro p hp
    exact ⟨hp.isPrime, ⟨(hcontract p hp).symm⟩⟩
  exact ⟨hredC, hfinite, hcontract⟩

end AlgebraicGeometry
