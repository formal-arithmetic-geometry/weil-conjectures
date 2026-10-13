/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P3
-/
module

public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs

/-!
# Finite-rank correction of a lifted coefficient section

Source: Stacks Project, Tag 07FG, the derivation and Jacobi--Zariski paragraphs.
(blueprint: lem-weil-pbc-finite-rank-coefficient-correction)
-/

@[expose] public section

set_option autoImplicit false

universe u v w

namespace Algebra

/-- Given two structure maps agreeing modulo an annihilated ideal, adjust an existing
residue section so their discrepancy has finite rank over the base field. The fixed
coefficient field is not enlarged here; the finite error generators still lie in I.

Source: Stacks Project, Tag 07FG, from "These maps agree modulo I" through the formula
expressing theta(a) as a finite sum of a_j f_j.
(blueprint: lem-weil-pbc-finite-rank-coefficient-correction).

Proof:
1. Give I its K-vector-space structure through r; this is well defined because ker(r)I=0.
   The difference theta = algebraMap k Lambda - psi takes values in I. The product
   identity for two ring maps, and the fact their difference belongs to I, show that
   theta is a derivation over the prime field, with scalar action through k -> K.
2. The differentials dy for y in k span Omega_{k/F_p}; choose a basis dy_j from them.
   They remain a basis after extension of scalars to K. Jacobi--Zariski exactness at
   K tensor Omega_k identifies the kernel of its map to Omega_K with the image of
   H1(K/k). Its finite dimension puts this kernel in the span of a finite subset J0
   of the extended basis. The remaining dy_j have independent images in Omega_K.
3. Extend those images to a basis of Omega_K. Define a K-linear map to I agreeing with
   theta on these basis vectors and zero on the added vectors. Its universal
   derivation D : K -> I makes theta - D restricted to k vanish on all dy_j outside
   J0. Put f_j equal to its values on dy_j for j in J0. Every value of the corrected
   derivation lies in the k-span of this finite family, all of which belong to I.
4. Set sigma = sigma0 + D. The identities I^2 = 0 and ker(r)I = 0 show it is a ring
   map, a section of r, and unchanged modulo I. For each a choose a polynomial
   expression for psi(a) in t and sigma0(k(c0)), which exists by the ring-closure
   hypothesis. Reevaluate it using sigma instead. Every positive-degree term has
   the same value, since t lies in ker(r) and D takes values in I. The change in
   its constant coefficient is D(r(psi(a))) = D(algebraMap k K a). The new value b
   lies in the closure using sigma and the same c0. Thus algebraMap k Lambda a - b
   is precisely the corrected derivation value, in the k-span of the finite f_j.
   Ring closure allows integer constants as well; D vanishes on them. -/
theorem exists_finite_rank_coefficient_correction
    (k : Type u) [Field k] (K : Type w) [Field K] [Algebra k K]
    (Λ : Type v) [CommRing Λ] [Algebra k Λ] [IsLocalRing Λ]
    (r : Λ →+* K) (hker : RingHom.ker r = IsLocalRing.maximalIdeal Λ)
    (hcomm : r.comp (algebraMap k Λ) = algebraMap k K)
    (t : Finset Λ) (ht : Ideal.span (t : Set Λ) = IsLocalRing.maximalIdeal Λ)
    (I : Ideal Λ) (hI : I ≤ RingHom.ker r)
    (hkill : IsLocalRing.maximalIdeal Λ * I = ⊥)
    (σ0 : K →+* Λ) (hσ0 : r.comp σ0 = RingHom.id K) (c0 : Finset K)
    (ψ : k →+* Λ)
    (hψ : (Ideal.Quotient.mk I).comp ψ =
      (Ideal.Quotient.mk I).comp (algebraMap k Λ))
    (hψmem : ∀ a : k, ψ a ∈ Subring.closure ((t : Set Λ) ∪
      σ0 '' (IntermediateField.adjoin k (c0 : Set K) : Set K)))
    (p : ℕ) [CharP k p] (hp : 0 < p)
    (hH : Module.Finite K (H1Cotangent k K)) :
    ∃ (σ : K →+* Λ) (f : Finset Λ),
      r.comp σ = RingHom.id K ∧
      (Ideal.Quotient.mk I).comp σ = (Ideal.Quotient.mk I).comp σ0 ∧
      (f : Set Λ) ⊆ I ∧
      (∀ a : k, ∃ b : Λ,
        b ∈ Subring.closure ((t : Set Λ) ∪
          σ '' (IntermediateField.adjoin k (c0 : Set K) : Set K)) ∧
        algebraMap k Λ a - b ∈ Submodule.span k (f : Set Λ)) := by sorry

end Algebra
