/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NV
-/
module

public import WeilConjectures.RingTheory.GRing
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.TensorProduct.Basic

import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import WeilConjectures.FieldTheory.CommonExtensionFields
import WeilConjectures.RingTheory.GeometricallyRegularFieldExtension
import WeilConjectures.RingTheory.RegularRingFaithfullyFlatDescent

/-!
# Finite surjective base change detects regularity of a flat ring map

Source: Silvio Greco, Two theorems on excellent rings, Nagoya Math. J. 60 (1976),
Proposition 1.2, converse, p. 140, with P = geometrically regular as in Definition 1.1
(blueprint: lem-per-regular-map-finite-surjective-detection).
-/

@[expose] public section

set_option autoImplicit false

universe u v w

namespace RingHom

/-- A flat map of Noetherian rings is regular if it becomes regular after a finite
base change that is surjective on prime spectra. The base-changed map is the canonical
inclusion `r' ↦ 1 ⊗ r'`, without imposing a second algebra structure on the tensor product.
Source: Greco, Two theorems on excellent rings, Proposition 1.2, converse, p. 140,
with P = geometrically regular in Definition 1.1
(blueprint: lem-per-regular-map-finite-surjective-detection).

Proof, following the six steps of the node:
1. For each prime p of R, choose a prime p' of R' contracting to p using `hsurj`.
   Set k = κ(p), L = κ(p'), C = Λ ⊗[R] k, and D = (Λ ⊗[R] R') ⊗[R'] L.
   The residue-field map k → L is well defined and injective: a denominator outside p
   maps outside p'. Regularity of the base-changed map says D is Noetherian and
   geometrically regular over L, by `def-weil-pbc-g-ring` and
   `def-weil-pbc-localization-at-prime`.
2. The tensor cancellation `lem-weil-pbc-tensor-cancel-base-change`, together with
   interchange of factors, identifies D with L ⊗[k] C as an L-algebra. On pure tensors
   it sends ((a ⊗ b) ⊗ ℓ) to ℓ b̄ ⊗ (a ⊗ 1), with inverse
   ℓ ⊗ (a ⊗ x) ↦ (a ⊗ 1) ⊗ ℓ x̄. The balancing relations make these inverse ring maps.
3. For an arbitrary finite purely inseparable K/k, including the identity extension,
   use `lem-weil-common-extension-fields` to place K and L in a common field over k.
   Their compositum M is finite over L, with degree at most [K:k], by
   `lem-weil-pbc-compositum-degree-bound`. Thus M/L is finitely generated as a field.
4. Apply `lem-weil-pbc-geometrically-regular-finitely-generated-extensions` to D over L
   and M/L. The resulting regular ring M ⊗[L] D is isomorphic to E ⊗[K] M,
   where E = K ⊗[k] C, by tensor cancellation and step 2. The isomorphism sends
   m ⊗ ((a ⊗ b) ⊗ ℓ) to (1 ⊗ (a ⊗ 1)) ⊗ m b̄ ℓ, with inverse
   (x ⊗ (a ⊗ y)) ⊗ m ↦ m x̄ ȳ ⊗ ((a ⊗ 1) ⊗ 1).
5. The map E → E ⊗[K] M is faithfully flat by
   `lem-weil-pbc-field-extension-base-change-faithfully-flat`. Descend regularity by
   `lem-weil-pbc-regular-ring-faithfully-flat-descent`. Hence K ⊗[k] C is regular for
   every finite purely inseparable K/k. The identity extension first gives that C is
   Noetherian, and the whole family gives geometric regularity over k.
6. Every fibre of the original map is therefore Noetherian and geometrically regular.
   Together with `hflat`, this is `RingHom.IsRegular` in `def-weil-pbc-g-ring`.
-/
theorem isRegular_of_finite_surjective_baseChange
    {R : Type u} {Λ : Type v} {R' : Type w}
    [CommRing R] [CommRing Λ] [CommRing R']
    [IsNoetherianRing R] [IsNoetherianRing Λ] [IsNoetherianRing R']
    [Algebra R Λ] [Algebra R R'] [Module.Finite R R']
    (hflat : (algebraMap R Λ).Flat)
    (hsurj : ∀ (p : Ideal R) [p.IsPrime],
      ∃ p' : Ideal R', p'.IsPrime ∧ Ideal.comap (algebraMap R R') p' = p)
    (hregular : RingHom.IsRegular
      (Algebra.TensorProduct.includeRight : R' →ₐ[R] TensorProduct R Λ R').toRingHom) :
    RingHom.IsRegular (algebraMap R Λ) := by
  sorry

end RingHom
