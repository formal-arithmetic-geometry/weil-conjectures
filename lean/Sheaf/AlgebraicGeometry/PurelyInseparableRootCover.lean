/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q5
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
public import Mathlib.RingTheory.AdjoinRoot
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.FieldTheory.Perfect
import WeilConjectures.Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

/-! # Finite radicial root covers

Source: Stacks Project, More on Morphisms, Tag 0GK7, the root-adjunction construction.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Polynomial
namespace AlgebraicGeometry

/-- Adjoining a p-th root in characteristic p gives a finite radicial surjection.
Source: Stacks Project, Tag 0GK7, the paragraph constructing Spec B[t]/(t^p-a).
(blueprint: lem-weil-pbc-purely-inseparable-root-cover)

Proof: The monic polynomial T^p-a has positive degree, so its root algebra is finite
free and faithfully flat over A. Thus its spectrum map is finite and surjective.
For universal injectivity, use the field-valued-point criterion. Two field points over
the same A-point give homomorphisms from the root algebra agreeing on A. The target
field has characteristic p. Both images of the adjoined root have p-th power equal
to the same image of a, so injectivity of Frobenius makes them equal. The universal
property of the root algebra says that the homomorphisms, and hence the points, agree.
This also covers the zero base ring: there are then no field-valued points. -/
theorem finite_radicial_root_cover (A : Type u) [CommRing A]
    (p : ℕ) (hp : p.Prime) [CharP A p] (a : A) :
    let g := Spec.map (CommRingCat.ofHom
      (algebraMap A (AdjoinRoot (X ^ p - C a : A[X]))))
    IsFinite g ∧ Surjective g ∧ UniversallyInjective g := by
  let g := Spec.map (CommRingCat.ofHom
    (algebraMap A (AdjoinRoot (X ^ p - C a : A[X]))))
  have hmonic := monic_X_pow_sub_C a hp.ne_zero
  have hfinite : IsFinite g := by
    change IsFinite (Spec.map (CommRingCat.ofHom (algebraMap A _)))
    rw [IsFinite.SpecMap_iff]
    exact RingHom.finite_algebraMap.mpr hmonic.finite_adjoinRoot
  have hsurj : Surjective g := by
    have hdeg : (X ^ p - C a : A[X]).degree ≠ 0 := by
      nontriviality A
      rw [degree_X_pow_sub_C hp.pos]
      exact_mod_cast hp.ne_zero
    exact ((flat_and_surjective_SpecMap_iff _).mpr
      (RingHom.faithfullyFlat_algebraMap_iff.mpr
        (AdjoinRoot.faithfullyFlat_of_monic hmonic hdeg))).2
  refine ⟨hfinite, hsurj, ?_⟩
  refine ((tfae_universallyInjective g).out 1 0).mp ?_
  intro Ω _ g₁ g₂ hg
  rw [← Spec.map_preimage g₁, ← Spec.map_preimage g₂] at hg ⊢
  simp only [g, ← Spec.map_comp] at hg
  have hc := congrArg CommRingCat.Hom.hom (Spec.map_injective hg)
  let α := (Spec.preimage g₁).hom
  let β := (Spec.preimage g₂).hom
  have : CharP Ω p := (CharP.charP_iff_prime_eq_zero hp).mpr (by
    have hz : (p : A) = 0 := CharP.cast_eq_zero A p
    simpa only [map_natCast, map_zero] using
      congrArg (α.comp (algebraMap A _)) hz)
  have : ExpChar Ω p := ExpChar.prime hp
  have hroot (φ : AdjoinRoot (X ^ p - C a : A[X]) →+* Ω) :
      φ (AdjoinRoot.root _) ^ p = φ (algebraMap A _ a) := by
    have hr := AdjoinRoot.eval₂_root (X ^ p - C a : A[X])
    simp only [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, sub_eq_zero] at hr
    rw [← map_pow, hr]
    rfl
  have heq : α (AdjoinRoot.root _) = β (AdjoinRoot.root _) := by
    apply frobenius_inj Ω p
    change α (AdjoinRoot.root _) ^ p = β (AdjoinRoot.root _) ^ p
    rw [hroot, hroot]
    exact RingHom.congr_fun hc a
  congr 1
  apply CommRingCat.hom_ext
  exact AdjoinRoot.ringHom_ext hc heq

end AlgebraicGeometry
