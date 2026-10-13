/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H2
-/
module

public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.Algebra.Category.ModuleCat.Basic
import Sheaf.RingTheory.FormalGlueingEquivalence

/-!
# Algebraization of a map that is an isomorphism away from an ideal

Source: Stacks Project, More on Algebra, Lemma 0ALK, proof of part (2),
using Remark 05EL and Proposition 05ER 
(blueprint: lem-weil-pbc-formal-glueing-map-from-algebraization).
-/

@[expose] public section

universe u v w

open scoped TensorProduct

namespace FormalGlueing

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/-- Algebraize the map and retain ideal-power torsion of its kernel and cokernel.
Source: Stacks Project, More on Algebra, Lemma 0ALK, proof of part (2),
with Remark 05EL and Proposition 05ER 
(blueprint: lem-weil-pbc-formal-glueing-map-from-algebraization).

Choose a finite generating family of I. At each generator f, every torsion element
vanishes after localization: an annihilating ideal power supplies an annihilating
power of f. Exact localization therefore makes the given map bijective on each
chart. Start with the canonical datum of P, replace its S-component by Q, and
compose its comparison with the localized given map's inverse.
The overlap and cocycle identities follow from those for the canonical datum and
naturality of localization. The given map and the identity chart maps form a
morphism of data from the canonical datum. Essential surjectivity of the canonical equivalence
algebraizes the modified datum. Fullness algebraizes that morphism; its first
component gives the displayed factorization, and each chart component is an
isomorphism. Exact localization now makes the kernel and cokernel of the descended
map vanish on every chart. For any element choose positive exponents e_i killing
it at the finitely many generators. Every monomial of degree 1 + sum e_i contains
one generator to at least its e_i-th power, so that power of I kills the element.
If there are no generators then I = 0, and its first power already kills every
element. This proves both torsion assertions. No comparison equivalence is asserted
here; those are proved separately using flat tensor exactness and torsion base change.
-/
theorem exists_map_from_algebraization
    (hflat : (algebraMap R S).Flat) (I : Ideal R) (hI : I.FG)
    (hquot : Function.Bijective
      (Ideal.quotientMap (I.map (algebraMap R S)) (algebraMap R S) Ideal.le_comap_map))
    (P : Type (max u v w)) [AddCommGroup P] [Module R P]
    (Q : Type (max u v w)) [AddCommGroup Q] [Module S Q] [Module R Q]
    [IsScalarTower R S Q]
    (φ' : S ⊗[R] P →ₗ[S] Q)
    (hker : ∀ x : (φ'.restrictScalars R).ker,
      ∃ n : ℕ, ∀ r ∈ I ^ n, r • x = 0)
    (hcoker : ∀ x : _ ⧸ (φ'.restrictScalars R).range,
      ∃ n : ℕ, ∀ r ∈ I ^ n, r • x = 0) :
    ∃ T : ModuleCat.{max u v w} R,
      ∃ (ψ : P →ₗ[R] T) (β : S ⊗[R] T ≃ₗ[S] Q),
        β.toLinearMap.comp (ψ.baseChange S) = φ' ∧
        (∀ x : ψ.ker, ∃ n : ℕ, ∀ r ∈ I ^ n, r • x = 0) ∧
        (∀ x : T ⧸ ψ.range, ∃ n : ℕ, ∀ r ∈ I ^ n, r • x = 0) := by
  sorry

end FormalGlueing
