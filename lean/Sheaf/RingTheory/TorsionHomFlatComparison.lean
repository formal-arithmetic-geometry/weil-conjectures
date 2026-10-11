/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N1
-/
module

public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# Hom comparison for a torsion source along a flat neighbourhood

Source: Stacks Project, More on Algebra, Lemma 05EC, part (2), torsion-source case
(blueprint: lem-weil-pbc-torsion-hom-flat-comparison).

Mathlib writes scalar extension as `S ⊗[R] K`; tensor symmetry identifies this with
`K ⊗[R] S` in the source. The algebra structure encodes the arbitrary ring map.
-/

@[expose] public section

universe u v w x

open scoped TensorProduct

namespace LinearMap

/-- Scalar extension gives a bijection on Hom sets when the source is ideal-power torsion;
the bijection is `LinearMap.baseChange`, natural in both modules by `LinearMap.baseChange_comp`.
Source: Stacks Project, More on Algebra, Lemma 05EC, part (2), torsion-source case
(blueprint: lem-weil-pbc-torsion-hom-flat-comparison).

Proof:
1. For a torsion target T, its canonical map to S ⊗ T is bijective by
   lem-weil-pbc-torsion-module-flat-base-change-iso. The scalar-extension adjunction
   lem-weil-pbc-scalar-extension-hom identifies Hom_S(S ⊗ K, S ⊗ T) with
   Hom_R(K, S ⊗ T). Composition with the canonical map identifies the latter with
   Hom_R(K,T). On pure tensors the resulting comparison is LinearMap.baseChange.
2. For an arbitrary N let T = N[I^infinity]. By finite generation of I and
   lem-weil-pbc-torsion-submodule-flat-base-change-iso, T maps bijectively onto the
   ideal-power torsion submodule of S ⊗ N. The torsion-module comparison also identifies
   T with S ⊗ T, so the tensor of T's inclusion is injective with that exact image.
   The same comparison shows S ⊗ K is IS-power torsion.
3. Every map from K to N factors uniquely through T; every S-linear map from S ⊗ K
   to S ⊗ N factors uniquely through S ⊗ T. The resulting Hom comparison square commutes
   on pure tensors. The torsion-target case from step 1 gives bijectivity in general.
   Naturality in both modules is that of `LinearMap.baseChange` itself
   (`LinearMap.baseChange_comp`), so the statement carries it by naming the map. -/
theorem baseChange_bijective_of_ideal_power_torsion
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (_hflat : (algebraMap R S).Flat) (I : Ideal R) (_hI : I.FG)
    (_hquot : Function.Bijective
      (Ideal.quotientMap (I.map (algebraMap R S)) (algebraMap R S) Ideal.le_comap_map))
    {K : Type w} {N : Type x} [AddCommGroup K] [AddCommGroup N]
    [Module R K] [Module R N]
    (_hK : ∀ k : K, ∃ n : ℕ, ∀ r ∈ I ^ n, r • k = 0) :
    Function.Bijective (LinearMap.baseChange S : (K →ₗ[R] N) →
      (S ⊗[R] K →ₗ[S] S ⊗[R] N)) := by
  sorry

end LinearMap
