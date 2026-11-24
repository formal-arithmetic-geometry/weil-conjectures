/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.RingTheory.Finiteness.Defs

import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RingTheory.Finiteness.Basic

/-!
# Linear extension with finite error over the smaller field

## References

* Stacks Project, Tag 07FG.
-/

@[expose] public section
set_option autoImplicit false
open scoped TensorProduct
universe u v w x y

namespace LinearMap

/-- A linear map from the original vector space can be extended through a map on its
scalar extension, up to an error of finite rank over the original field. -/
theorem exists_extension_finite_error
    (k : Type u) [Field k] (K : Type v) [Field K] [Algebra k K]
    (V : Type w) [AddCommGroup V] [Module k V]
    (W : Type x) [AddCommGroup W] [Module k W] [Module K W] [IsScalarTower k K W]
    (M : Type y) [AddCommGroup M] [Module k M] [Module K M] [IsScalarTower k K M]
    (phi : K ⊗[k] V →ₗ[K] W) (hphi : Module.Finite K phi.ker)
    (ell : V →ₗ[k] M) :
    ∃ (g : W →ₗ[K] M) (f : Finset M),
      ∀ v : V, ell v - g (phi (1 ⊗ₜ[k] v)) ∈ Submodule.span k (f : Set M) := by
  classical
  let b := Module.Free.chooseBasis k V
  let B := b.baseChange K
  have : Module.Finite K phi.ker := hphi
  obtain ⟨t, ht⟩ := Submodule.FG.of_finite (N := phi.ker)
  let s := t.biUnion fun z ↦ (B.repr z).support
  have hker : phi.ker ≤ Submodule.span K (B '' (s : Set (Module.Free.ChooseBasisIndex k V))) := by
    rw [← ht, Submodule.span_le]
    intro z hz
    apply (B.mem_span_image).mpr
    intro i hi
    exact Finset.mem_biUnion.mpr ⟨z, hz, hi⟩
  let J := {i : Module.Free.ChooseBasisIndex k V // i ∉ s}
  have hdis : Disjoint (Submodule.span K (Set.range fun i : J ↦ B i.val)) phi.ker := by
    have hd := B.linearIndependent.disjoint_span_image
      (s := {i | i ∉ s}) (t := (s : Set _)) (by exact Set.disjoint_left.mpr fun _ h hn ↦ h hn)
    apply Disjoint.mono_right hker
    convert hd using 1
    congr 1
    ext z
    simp [J]
  have hli : LinearIndependent K (fun i : J ↦ phi (B i.val)) :=
    (B.linearIndependent.comp Subtype.val Subtype.val_injective).map hdis
  let c := Module.Basis.span hli
  let q := c.constr K (fun i : J ↦ ell (b i.val))
  obtain ⟨g, hg⟩ := q.exists_extend
  have hgB (i : J) : g (phi (B i.val)) = ell (b i.val) := by
    have he := LinearMap.congr_fun hg (c i)
    change g (c i : W) = (c.constr K (fun j : J ↦ ell (b j.val))) (c i) at he
    rw [Module.Basis.constr_basis] at he
    simpa only [c, Module.Basis.span_apply] using he
  let j : V →ₗ[k] K ⊗[k] V := TensorProduct.mk k K V 1
  let delta : V →ₗ[k] M := ell -
    (g.restrictScalars k).comp ((phi.restrictScalars k).comp j)
  let f := s.image (fun i ↦ delta (b i))
  refine ⟨g, f, ?_⟩
  have hb (i : Module.Free.ChooseBasisIndex k V) :
      delta (b i) ∈ Submodule.span k (f : Set M) := by
    by_cases hi : i ∈ s
    · exact Submodule.subset_span (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
    · have he := hgB ⟨i, hi⟩
      have hz : delta (b i) = 0 := by
        simpa only [delta, LinearMap.sub_apply, LinearMap.comp_apply,
          LinearMap.restrictScalars_apply, j, TensorProduct.mk_apply,
          Module.Basis.baseChange_apply, B, sub_eq_zero] using he.symm
      rw [hz]
      exact Submodule.zero_mem _
  have hle : (⊤ : Submodule k V) ≤ (Submodule.span k (f : Set M)).comap delta := by
    rw [← b.span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact hb i
  intro v
  exact hle (show v ∈ (⊤ : Submodule k V) from trivial)


end LinearMap
