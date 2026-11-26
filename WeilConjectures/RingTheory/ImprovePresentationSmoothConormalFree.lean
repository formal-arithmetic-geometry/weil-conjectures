/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.Algebra.MvPolynomial.Basic
import WeilConjectures.RingTheory.SymmetricAlgebraSmooth
import WeilConjectures.RingTheory.SymmetricConormalFreePresentation
import Mathlib.RingTheory.Finiteness.Small

/-!
# Smooth presentation with free conormal module

A smooth algebra `A` is a retract of a smooth `A`-algebra `C` that admits a polynomial
presentation with free conormal module.

## Implementation details

`C` is the symmetric algebra of the (finite projective) conormal module of a finite presentation
of `A`, shrunk to the universe of `A`. The presentation of `C` evaluates the first variables at
the generators of `A` and the remaining ones at the degree-one classes of the relations.

## References

* [Stacks, Tag 07CE]
-/

@[expose] public section

universe u v

namespace Algebra

/--
A smooth `R`-algebra `A` is a retract of a smooth `A`-algebra `C` admitting a surjection
`R[x₁, …, xₘ] → C` whose kernel `J` has free conormal module `J/J²`.
-/
theorem improve_presentation_smooth_conormal_free
    (R : Type u) [CommRing R] (A : Type v) [CommRing A] [Algebra R A]
    [Smooth R A] :
    ∃ (C : Type v) (_ : CommRing C) (_ : Algebra R C) (_ : Algebra A C)
      (_ : IsScalarTower R A C) (_ : Smooth A C),
      ∃ (ρ : C →ₐ[A] A),
        ρ.comp (Algebra.ofId A C) = AlgHom.id A A ∧
      ∃ (m : ℕ) (f : MvPolynomial (Fin m) R →ₐ[R] C),
        Function.Surjective f ∧
        ∃ (J : Ideal (MvPolynomial (Fin m) R)),
          J = RingHom.ker f.toRingHom ∧
          Module.Free (MvPolynomial (Fin m) R ⧸ J) J.Cotangent := by
  classical
  obtain ⟨n, m, ⟨P⟩⟩ := Presentation.exists_presentation_fin R A
  have : FormallySmooth R P.toExtension.Ring := by
    change FormallySmooth R (MvPolynomial (Fin n) R)
    infer_instance
  obtain ⟨l, hl⟩ := P.toExtension.formallySmooth_iff_split_injection.mp
    (inferInstance : FormallySmooth R A)
  have : Module.Projective A P.toExtension.Cotangent :=
    Module.Projective.of_split P.toExtension.cotangentComplex l hl
  have : Module.Finite A P.toExtension.Cotangent :=
    Extension.Cotangent.finite (P := P.toExtension) P.fg_ker
  have : Small.{v} P.toExtension.Cotangent :=
    Module.Finite.small A P.toExtension.Cotangent
  let M := Shrink.{v} P.toExtension.Cotangent
  let C := SymmetricAlgebra A M
  let : Algebra R C := ((algebraMap A C).comp (algebraMap R A)).toAlgebra
  have : IsScalarTower R A C := IsScalarTower.of_algebraMap_eq' rfl
  have : Module.Finite A M :=
    Module.Finite.equiv (Shrink.linearEquiv A P.toExtension.Cotangent).symm
  have : Smooth A C := SymmetricAlgebra.smooth_of_finite_projective A M
  let ρ : C →ₐ[A] A := SymmetricAlgebra.lift (0 : M →ₗ[A] A)
  let e := (Shrink.linearEquiv A P.toExtension.Cotangent).symm
  let x : Fin m → M := fun j ↦ e (Extension.Cotangent.mk
    ⟨P.relation j, P.relation_mem_ker j⟩)
  let f : MvPolynomial (Fin (n + m)) R →ₐ[R] C :=
    MvPolynomial.aeval (fun i ↦ Sum.elim
      (fun j ↦ algebraMap A C (P.val j))
      (fun j ↦ SymmetricAlgebra.ι A M (x j)) (finSumFinEquiv.symm i))
  have hfree := P.symmetric_conormal_free_presentation M e
  have hfA : f.comp (MvPolynomial.rename
      (fun j : Fin n ↦ finSumFinEquiv (Sum.inl j))) =
      ((Algebra.ofId A C).restrictScalars R).comp
        (MvPolynomial.aeval P.val) := by
    apply MvPolynomial.algHom_ext
    intro j
    simp [f]
  have hA (a : A) : algebraMap A C a ∈ f.range := by
    obtain ⟨p, hp⟩ := P.aeval_val_surjective a
    refine ⟨MvPolynomial.rename (fun j : Fin n ↦ finSumFinEquiv (Sum.inl j)) p, ?_⟩
    change (f.comp (MvPolynomial.rename _)) p = _
    rw [hfA]
    change algebraMap A C (MvPolynomial.aeval P.val p) = _
    rw [hp]
  have hx : Submodule.span A (Set.range x) = ⊤ := by
    have h := Extension.Cotangent.span_eq_top_of_span_eq_ker
      (P := P.toExtension) P.relation P.span_range_relation_eq_ker
    have hm := congrArg (Submodule.map e.toLinearMap) h
    simpa [Submodule.map_span, ← Set.range_comp, x, Function.comp_def] using hm
  have hι (z : M) : SymmetricAlgebra.ι A M z ∈ f.range := by
    have hz : z ∈ Submodule.span A (Set.range x) := by rw [hx]; trivial
    refine Submodule.span_induction
      (p := fun z _ ↦ SymmetricAlgebra.ι A M z ∈ f.range) ?_ ?_ ?_ ?_ hz
    · rintro z ⟨j, rfl⟩
      refine ⟨MvPolynomial.X (finSumFinEquiv (Sum.inr j)), ?_⟩
      simp [f]
    · simp
    · intro z w hz hw ihz ihw
      simpa only [map_add] using f.range.add_mem ihz ihw
    · intro a z hz ihz
      rw [map_smul, Algebra.smul_def]
      exact f.range.mul_mem (hA a) ihz
  have hf : Function.Surjective f := by
    intro c
    change c ∈ f.range
    induction c using SymmetricAlgebra.induction with
    | algebraMap a => exact hA a
    | ι z => exact hι z
    | mul z w hz hw => exact f.range.mul_mem hz hw
    | add z w hz hw => exact f.range.add_mem hz hw
  refine ⟨C, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    ρ, ?_, n + m, f, hf, RingHom.ker f.toRingHom, rfl, hfree⟩
  apply AlgHom.ext
  intro a
  exact ρ.commutes a

end Algebra
