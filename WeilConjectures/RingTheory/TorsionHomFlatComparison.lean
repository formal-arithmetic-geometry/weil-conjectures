/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.LinearAlgebra.TensorProduct.Tower
import WeilConjectures.Algebra.Module.TorsionSubmoduleFlatBaseChangeIso

/-!
# Hom comparison for a torsion source along a flat neighbourhood

For a flat ring map `R → S` inducing an isomorphism `R / I ≅ S / IS`, scalar extension gives a
bijection on Hom sets out of an `I`-power torsion module.

## Implementation details

Mathlib writes scalar extension as `S ⊗[R] K`; tensor symmetry identifies this with
`K ⊗[R] S`. The algebra structure encodes the arbitrary ring map.

The proof first treats a torsion target `T`, where `T → S ⊗ T` is bijective and the
scalar-extension adjunction identifies the Hom sets. For general `N`, every map out of `K`
factors uniquely through the `I`-power torsion submodule of `N`, whose base change is the
`IS`-power torsion submodule of `S ⊗ N`. Naturality in both modules is that of
`LinearMap.baseChange` (`LinearMap.baseChange_comp`).

## References

* [Stacks, Tag 05EC]
-/

@[expose] public section

universe u v w x

open scoped TensorProduct

namespace LinearMap

/-- Let `R → S` be flat with `R / I ≅ S / IS` for a finitely generated ideal `I`. If `K` is
`I`-power torsion, then scalar extension `LinearMap.baseChange` is a bijection
`Hom_R(K, N) → Hom_S(S ⊗[R] K, S ⊗[R] N)`. -/
theorem baseChange_bijective_of_ideal_power_torsion
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (hflat : (algebraMap R S).Flat) (I : Ideal R) (hI : I.FG)
    (hquot : Function.Bijective
      (Ideal.quotientMap (I.map (algebraMap R S)) (algebraMap R S) Ideal.le_comap_map))
    {K : Type w} {N : Type x} [AddCommGroup K] [AddCommGroup N]
    [Module R K] [Module R N]
    (hK : ∀ k : K, ∃ n : ℕ, ∀ r ∈ I ^ n, r • k = 0) :
    Function.Bijective (LinearMap.baseChange S : (K →ₗ[R] N) →
      (S ⊗[R] K →ₗ[S] S ⊗[R] N)) := by
  classical
  let c : N →ₗ[R] S ⊗[R] N := TensorProduct.mk R S N 1
  let t := Ideal.primaryComponent.map I c
  have ht : Function.Bijective t :=
    Ideal.primaryComponent_baseChange_bijective I hI hflat hquot N
  have hmem (k : K) : k ∈ Ideal.primaryComponent K I := by
    obtain ⟨n, hn⟩ := hK k
    exact (Ideal.primaryComponent_mem K I k).2
      ⟨n, (Submodule.mem_torsionBySet_iff _ _).2 (fun r ↦ hn r r.property)⟩
  constructor
  · intro f g hfg
    ext k
    have hf := Ideal.primaryComponent_map_mem I f ⟨k, hmem k⟩
    have hg := Ideal.primaryComponent_map_mem I g ⟨k, hmem k⟩
    have heq : t ⟨f k, hf⟩ = t ⟨g k, hg⟩ := by
      apply Subtype.ext
      exact congrArg (fun l : S ⊗[R] K →ₗ[S] S ⊗[R] N ↦ l (1 ⊗ₜ[R] k)) hfg
    exact congrArg Subtype.val (ht.1 heq)
  · intro g
    let d : K →ₗ[R] S ⊗[R] N :=
      (g.restrictScalars R).comp (TensorProduct.mk R S K 1)
    let d' : K →ₗ[R] Ideal.primaryComponent (S ⊗[R] N) I :=
      d.codRestrict _ (fun k ↦ Ideal.primaryComponent_map_mem I d ⟨k, hmem k⟩)
    let e := LinearEquiv.ofBijective t ht
    let f : K →ₗ[R] N :=
      (Ideal.primaryComponent N I).subtype.comp (e.symm.toLinearMap.comp d')
    have hf (k : K) : c (f k) = d k := by
      exact congrArg Subtype.val (e.apply_symm_apply (d' k))
    refine ⟨f, ?_⟩
    apply TensorProduct.AlgebraTensorModule.ext
    intro s k
    calc
      f.baseChange S (s ⊗ₜ[R] k) = s • c (f k) := by
        simp [c, TensorProduct.smul_tmul']
      _ = s • d k := congrArg (fun z ↦ s • z) (hf k)
      _ = g (s ⊗ₜ[R] k) := by
        simp [d, ← g.map_smul, TensorProduct.smul_tmul']

end LinearMap
