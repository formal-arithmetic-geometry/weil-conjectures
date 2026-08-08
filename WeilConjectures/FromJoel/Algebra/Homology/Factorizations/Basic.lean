/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.Factorizations.Basic
public import Mathlib.Algebra.Homology.CochainComplexOpposite
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.EpiWithInjectiveKernel

/-!
# Degreewise monomorphisms with projective cokernel

Supplement to `Mathlib.Algebra.Homology.Factorizations.Basic`, migrated from
the branch `jriou_localization` of Joël Riou's mathlib fork
(leanprover-community/mathlib4#25848), adapted to mathlib `v4.32.0`.

-/

@[expose] public section

open CategoryTheory Abelian Limits

variable {C : Type*} [Category C] [Abelian C]

namespace CochainComplex

/-- A morphism of cochain complexes `φ` in an abelian category satisfies
`degreewiseMonoWithProjectiveCokernel φ` if for any `i : ℤ`, the morphism
`φ.f i` is a monomorphism with a projective cokernel. -/
def degreewiseMonoWithProjectiveCokernel : MorphismProperty (CochainComplex C ℤ) :=
  fun _ _ φ => ∀ (i : ℤ), monoWithProjectiveCokernel (φ.f i)

lemma degreewiseMonoWithProjectiveCokernel.mono {K L : CochainComplex C ℤ} {f : K ⟶ L}
    (hf : degreewiseMonoWithProjectiveCokernel f) :
    Mono f :=
  HomologicalComplex.mono_of_mono_f f (fun n ↦ (hf n).1)

lemma degreewiseMonoWithProjectiveCokernel_eq_unop :
    degreewiseMonoWithProjectiveCokernel (C := C) =
      (degreewiseEpiWithInjectiveKernel (C := Cᵒᵖ)).op.inverseImage
        (opEquivalence C).functor.rightOp := by
  ext K L f
  simp only [degreewiseMonoWithProjectiveCokernel, monoWithProjectiveCokernel_eq_unop,
    MorphismProperty.unop, MorphismProperty.inverseImage_iff, MorphismProperty.op,
    degreewiseEpiWithInjectiveKernel, Functor.rightOp_map]
  refine ⟨fun h n ↦ h _, fun h n ↦ ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = - m := ⟨-n, by simp⟩
  apply h

instance : (degreewiseMonoWithProjectiveCokernel (C := C)).IsMultiplicative := by
  rw [degreewiseMonoWithProjectiveCokernel_eq_unop]
  infer_instance

instance : (degreewiseMonoWithProjectiveCokernel (C := C)).IsStableUnderRetracts := by
  rw [degreewiseMonoWithProjectiveCokernel_eq_unop]
  infer_instance

lemma degreewiseMonoWithProjectiveCokernel_iff_of_isZero {K L : CochainComplex C ℤ}
    (f : K ⟶ L) (hK : IsZero K) :
    degreewiseMonoWithProjectiveCokernel f ↔ ∀ (n : ℤ), Projective (L.X n) :=
  forall_congr' (fun n ↦ by
    rw [monoWithProjectiveCokernel_iff_of_isZero]
    exact Functor.map_isZero (HomologicalComplex.eval _ _ n) hK)

end CochainComplex
