/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.Algebra.Module.FinitePresentation

/-!
# Base change of finitely presented quotients of free modules

For an `R`-algebra `S` and a family `a` of vectors in `ι → R` (`ι` finite), the base change
`S ⊗[R] ((ι → R) ⧸ span R (range a))` is `(ι → S) ⧸ span S (range (algebraMap R S ∘ a))`.

We also record that a finitely presented module is such a quotient (with `ι` and the family
finite), and conversely.
-/

@[expose] public section

open TensorProduct

namespace Submodule

/-- The image of a vector in the span of a family of vectors `a` under a ring homomorphism
`f`, applied coordinatewise, lies in the span of the images of `a`. -/
theorem map_mem_span_range {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) {ι κ : Type*}
    (a : κ → ι → R) {v : ι → R} (hv : v ∈ span R (Set.range a)) :
    (fun i ↦ f (v i)) ∈ span S (Set.range fun l i ↦ f (a l i)) := by
  set L := span S (Set.range fun l i ↦ f (a l i))
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨l, rfl⟩ := hx
    exact Submodule.subset_span ⟨l, rfl⟩
  | zero => simpa using L.zero_mem
  | add x y _ _ hx hy => simpa [Pi.add_def] using L.add_mem hx hy
  | smul r x _ hx =>
    convert L.smul_mem (f r) hx using 1
    ext i
    simp

end Submodule

namespace TensorProduct

/-- **Base change of a quotient of a finite free module.** For an `R`-algebra `S` and a family
`a : κ → ι → R` with `ι` finite, `S ⊗[R] ((ι → R) ⧸ ⟨a⟩) ≃ (ι → S) ⧸ ⟨algebraMap R S ∘ a⟩`,
sending `1 ⊗ [v]` to `[algebraMap R S ∘ v]`. -/
theorem exists_tensorQuotientSpanEquiv {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    {ι κ : Type*} [Finite ι] (a : κ → ι → R) :
    ∃ e : S ⊗[R] ((ι → R) ⧸ Submodule.span R (Set.range a)) ≃ₗ[S]
        (ι → S) ⧸ Submodule.span S (Set.range fun l i ↦ algebraMap R S (a l i)),
      ∀ v : ι → R, e (1 ⊗ₜ Submodule.Quotient.mk v) =
        Submodule.Quotient.mk (fun i ↦ algebraMap R S (v i)) := by
  classical
  have := Fintype.ofFinite ι
  let K := Submodule.span R (Set.range a)
  let L := Submodule.span S (Set.range fun l i ↦ algebraMap R S (a l i))
  let e₁ := AlgebraTensorModule.tensorQuotientEquiv S R S K
  let e₂ := TensorProduct.piScalarRight R S S ι
  have he₂ (s : S) (v : ι → R) : e₂ (s ⊗ₜ v) = s • fun i ↦ algebraMap R S (v i) := by
    ext i
    simp [e₂, Algebra.smul_def, mul_comm]
  have hK (v : ι → R) (hv : v ∈ K) : (fun i ↦ algebraMap R S (v i)) ∈ L :=
    Submodule.map_mem_span_range (algebraMap R S) a hv
  have h : (LinearMap.range (AlgebraTensorModule.lTensor S S
      (K.subtype.restrictScalars R))).map e₂.toLinearMap = L := by
    apply le_antisymm
    · rintro _ ⟨x, ⟨y, rfl⟩, rfl⟩
      induction y using TensorProduct.induction_on with
      | zero => simpa using L.zero_mem
      | tmul s k =>
        obtain ⟨k, hk⟩ := k
        have := L.smul_mem s (hK k hk)
        simpa [he₂] using this
      | add x y hx hy => simpa using L.add_mem hx hy
    · rw [Submodule.span_le]
      rintro _ ⟨l, rfl⟩
      refine ⟨(1 : S) ⊗ₜ ⟨a l, Submodule.subset_span ⟨l, rfl⟩⟩, ⟨_, rfl⟩, ?_⟩
      simp [he₂]
  refine ⟨e₁.trans (Submodule.Quotient.equiv _ _ e₂ h), fun v ↦ ?_⟩
  simp [e₁, he₂]

end TensorProduct

namespace Module.FinitePresentation

/-- A finitely presented module is the quotient of a finite free module `Fin n → R` by the span
of finitely many vectors. -/
theorem exists_linearEquiv_quotient_span {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] [Module.FinitePresentation R M] :
    ∃ (n r : ℕ) (a : Fin r → Fin n → R),
      Nonempty (((Fin n → R) ⧸ Submodule.span R (Set.range a)) ≃ₗ[R] M) := by
  obtain ⟨n, K, e, hK⟩ := Module.FinitePresentation.exists_fin R M
  obtain ⟨r, a, ha⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hK
  exact ⟨n, r, a, ⟨(Submodule.quotEquivOfEq _ _ ha).trans e.symm⟩⟩

/-- The quotient of a finite free module by the span of finitely many vectors is finitely
presented. -/
instance quotient_span {R : Type*} [CommRing R] {ι κ : Type*} [Finite ι] [Finite κ]
    (a : κ → ι → R) :
    Module.FinitePresentation R ((ι → R) ⧸ Submodule.span R (Set.range a)) :=
  Module.finitePresentation_of_surjective _ (Submodule.mkQ_surjective _)
    (by rw [Submodule.ker_mkQ]; exact Submodule.fg_span (Set.finite_range a))

end Module.FinitePresentation
