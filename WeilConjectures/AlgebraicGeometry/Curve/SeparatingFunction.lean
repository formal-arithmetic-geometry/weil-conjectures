/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.Etale.Kaehler
public import Mathlib.RingTheory.Unramified.Basic
public import WeilConjectures.Mathlib.RingTheory.Smooth.StandardSmoothCotangent

/-!
# Separating rational functions on smooth curves

Let `X` be an integral scheme smooth of relative dimension one over a field `k`, with function
field `K = k(X)`. Then `Ω[K⁄k]` is a one-dimensional `K`-vector space. A rational function `t`
with `dt ≠ 0` spans it, so that `K` is formally unramified over every subring containing `t`;
such a `t` can be chosen transcendental over `k`.

## Main statements

- `Algebra.FormallyUnramified.of_finrank_kaehlerDifferential_eq_one`: if `Ω[K⁄R]` is
  one-dimensional and `D t ≠ 0` for some `t` in the image of `A`, then `K` is formally
  unramified over `A`.
- `exists_transcendental_and_D_ne_zero`: if `Ω[K⁄R]` is one-dimensional and `K` has an element
  transcendental over `k`, then it has one `t` with `D t ≠ 0`.
- `AlgebraicGeometry.Scheme.finrank_kaehlerDifferential_functionField`: the Kähler differentials
  of the function field of an integral scheme smooth of relative dimension one over a field
  form a one-dimensional vector space.
-/

@[expose] public section

universe u

open CategoryTheory KaehlerDifferential

section Algebra

/-- If `Ω[K⁄R]` is one-dimensional over the field `K` and `D t ≠ 0` for some `t` in the image of
an intermediate ring `A`, then `K` is formally unramified over `A`: `Ω[K⁄A]` is the quotient of
`Ω[K⁄R] = K ⬝ D t` by the differentials of elements of `A`. -/
theorem Algebra.FormallyUnramified.of_finrank_kaehlerDifferential_eq_one {R A K : Type*}
    [CommRing R] [CommRing A] [Field K] [Algebra R A] [Algebra A K] [Algebra R K]
    [IsScalarTower R A K] (h : Module.finrank K Ω[K⁄R] = 1) {t : K} (ht : D R K t ≠ 0)
    (htA : t ∈ Set.range (algebraMap A K)) : Algebra.FormallyUnramified A K := by
  refine ⟨subsingleton_of_forall_eq 0 fun x ↦ ?_⟩
  obtain ⟨y, rfl⟩ := KaehlerDifferential.map_surjective R A K x
  obtain ⟨c, rfl⟩ := (finrank_eq_one_iff_of_nonzero' _ ht).mp h y
  obtain ⟨a, rfl⟩ := htA
  rw [LinearMap.map_smul, KaehlerDifferential.map_D, Algebra.algebraMap_self, RingHom.id_apply,
    Derivation.map_algebraMap, smul_zero]

/-- If `Ω[K⁄R]` is one-dimensional over the field `K` and `K` has an element transcendental over
a field `k`, then `K` has an element `t` transcendental over `k` with `D t ≠ 0`. -/
theorem exists_transcendental_and_D_ne_zero {k R K : Type*} [Field k] [CommRing R] [Field K]
    [Algebra k K] [Algebra R K] (h : Module.finrank K Ω[K⁄R] = 1) {s : K}
    (hs : Transcendental k s) : ∃ t : K, Transcendental k t ∧ D R K t ≠ 0 := by
  obtain ⟨u, hu⟩ : ∃ u : K, D R K u ≠ 0 := by
    by_contra! H
    have : (⊤ : Submodule K Ω[K⁄R]) = ⊥ := by
      rw [← KaehlerDifferential.span_range_derivation, Submodule.span_eq_bot]
      rintro _ ⟨u, rfl⟩
      exact H u
    have : Subsingleton Ω[K⁄R] := subsingleton_of_forall_eq 0 fun x ↦ by
      simpa using (this ▸ Submodule.mem_top : x ∈ (⊥ : Submodule K Ω[K⁄R]))
    simp [Module.finrank_zero_of_subsingleton] at h
  by_cases hDs : D R K s = 0
  swap
  · exact ⟨s, hs, hDs⟩
  by_cases hut : Transcendental k u
  · exact ⟨u, hut, hu⟩
  rw [Transcendental, not_not] at hut
  have hs0 : s ≠ 0 := fun h0 ↦ hs (h0 ▸ isAlgebraic_zero)
  have hu0 : u ≠ 0 := fun h0 ↦ hu (by rw [h0, map_zero])
  refine ⟨u * s, fun halg ↦ hs ?_, ?_⟩
  · have : s = u * s * u⁻¹ := by field_simp
    rw [this]
    exact halg.mul hut.inv
  · rw [Derivation.leibniz, hDs, smul_zero, zero_add]
    exact smul_ne_zero hs0 hu

end Algebra

namespace AlgebraicGeometry.Scheme

/-- The Kähler differentials of the function field `K` of an integral scheme `X` smooth of
relative dimension one over a field `k` form a one-dimensional `K`-vector space: on an affine
open `V` with `Γ(X, V)` standard smooth of relative dimension one, `Ω[Γ(X, V)⁄k]` is free of
rank one, and `Ω[K⁄k]` is its base change to the fraction field `K`. -/
theorem finrank_kaehlerDifferential_functionField {k : Type u} [Field k] {X : Scheme.{u}}
    [IsIntegral X] (f : X ⟶ Spec (.of k)) [SmoothOfRelativeDimension 1 f] :
    letI := (f.appTop ≫ X.presheaf.germ ⊤ (genericPoint X) trivial).hom.toAlgebra
    Module.finrank X.functionField Ω[X.functionField⁄Γ(Spec (.of k), ⊤)] = 1 := by
  obtain ⟨U, -, V, hV, hx, e, H⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension (n := 1) (f := f)
      (genericPoint X)
  obtain rfl : U = ⊤ := eq_top_iff.mpr fun z _ ↦ Subsingleton.elim (f (genericPoint X)) z ▸ e hx
  have : Nonempty V := ⟨⟨_, hx⟩⟩
  let := (f.appTop ≫ X.presheaf.germ ⊤ (genericPoint X) trivial).hom.toAlgebra
  let := (f.appLE ⊤ V e).hom.toAlgebra
  have : Algebra.IsStandardSmoothOfRelativeDimension 1 Γ(Spec (.of k), ⊤) Γ(X, V) := H
  have hfrac := functionField_isFractionRing_of_isAffineOpen X V hV
  have : IsScalarTower Γ(Spec (.of k), ⊤) Γ(X, V) X.functionField := by
    refine IsScalarTower.of_algebraMap_eq' ?_
    ext a
    change X.presheaf.germ ⊤ _ trivial (f.appTop a) =
      algebraMap Γ(X, V) X.functionField (f.appLE ⊤ V e a)
    simp only [Scheme.Hom.appLE]
    rw [CommRingCat.comp_apply]
    change _ = X.presheaf.germ V (genericPoint X) hx _
    rw [← CommRingCat.comp_apply (X.presheaf.map (homOfLE e).op), X.presheaf.germ_res]
    rfl
  have : Algebra.FormallyEtale Γ(X, V) X.functionField :=
    Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors Γ(X, V))
  obtain ⟨eΩ⟩ :=
    Algebra.IsStandardSmoothOfRelativeDimension.nonempty_linearEquiv_kaehlerDifferential
      (R := Γ(Spec (.of k), ⊤)) (S := Γ(X, V)) 1
  have : Module.Free Γ(X, V) Ω[Γ(X, V)⁄Γ(Spec (.of k), ⊤)] := Module.Free.of_equiv eΩ.symm
  rw [← (tensorKaehlerEquivOfFormallyEtale Γ(Spec (.of k), ⊤) Γ(X, V)
    X.functionField).finrank_eq, Module.finrank_baseChange, eΩ.finrank_eq,
    Module.finrank_fin_fun]

end AlgebraicGeometry.Scheme
