/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A2
-/
module

public import Mathlib.FieldTheory.Galois.Basic
public import Sheaf.AlgebraicGeometry.BaseChangeConventions
public import WeilConjectures.AlgebraicGeometry.Picard.Jacobian
import Sheaf.FieldTheory.TensorFieldExtensionGaloisInvariants

/-!
# Galois orbits in an affine base-change fibre

The fibres of a Galois base change are single Galois orbits. This is the scheme-level
form of transitivity of a profinite group on primes above its invariant ring.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Two points of a Galois base change with the same projection differ by a Galois
 automorphism. No closed subset, finiteness of the extension, or finite-type assumption
 on the scheme is required.

Source: Mathlib, `RingTheory/Invariant/Profinite.lean`,
`Algebra.IsInvariant.exists_smul_of_under_eq_of_profinite`; Stacks, Tag 0BRI for the
finite-group case, and Tag 038A for the contravariant scheme action.
(blueprint: lem-weil-pbc-affine-galois-base-change-fiber-transitivity).

Proof:
1. Write the affine scheme as `Spec A`, using its canonical `isoSpec`, and give `A`
   its `k`-algebra structure through the ring map corresponding to `f`. The pullback
   is `Spec (A ⊗[k] K)`, by `pullbackSpecIso`. The two points correspond to prime
   ideals with the same contraction to `A`; the action is `Spec (id_A ⊗ σ)`.
2. Equip `G = Aut(K/k)` with its Krull topology, which is profinite for any Galois
   algebraic extension, including an infinite one. Equip `A ⊗[k] K` with the discrete
   topology and let `G` act on the right tensor factor. Each tensor is a finite sum of
   pure tensors. The subgroup fixing its finitely many right-hand coefficients is
   open, so the action is continuous. The action commutes with the `A`-scalars.
3. The fixed field of `G` is `k`. Apply
   `TensorProduct.injective_and_range_eq_invariants` with the full automorphism group
   to the underlying vector space of `A`. Thus the invariant ring of the tensor
   product is precisely the image of `A`, giving `Algebra.IsInvariant A (A ⊗[k] K) G`.
4. Apply `Algebra.IsInvariant.exists_smul_of_under_eq_of_profinite` to the two primes.
   Its ideal action is direct image under the ring automorphism, whereas `Spec` uses
   inverse image. Replace the supplied automorphism by its inverse. Transport the
   resulting equality through the affine comparison. This gives exactly the displayed
   equality of points. -/
theorem exists_galois_map_eq_of_affine_projection_eq
    (k K : Type u) [Field k] [Field K] [Algebra k K] [IsGalois k K]
    (X : Scheme.{u}) [IsAffine X] (f : X ⟶ Spec (.of k))
    (x y : ↥(pullback f
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))))
    (hxy : (pullback.fst f
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))) x =
      (pullback.fst f
        (Spec.map (CommRingCat.ofHom (algebraMap k K)))) y) :
    ∃ σ : K ≃ₐ[k] K,
      (baseChangeMap f (specAlgEquivOver σ)) x = y := by sorry

end AlgebraicGeometry
