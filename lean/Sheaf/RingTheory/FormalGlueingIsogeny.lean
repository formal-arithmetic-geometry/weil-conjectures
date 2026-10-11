/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.Algebra.Category.ModuleCat.Basic

/-!
# Formal glueing of maps with ideal-power torsion kernel and cokernel

Source: Stacks Project, More on Algebra, Lemma 0ALK, with Lemmas 05EC and 05E9
(blueprint: lem-weil-pbc-formal-glueing-isogeny).

The tensor factors follow Mathlib's convention `S ⊗[R] M`. Ideal-power torsion
is expressed elementwise, and the comparison equivalences are specified on
kernel elements and on representatives of the cokernel.
-/

universe u v w

open scoped TensorProduct

namespace FormalGlueing

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/-- Part (1) and the comparisons in part (3) of Stacks, Lemma 0ALK;
Lemmas 05EC and 05E9 (blueprint: lem-weil-pbc-formal-glueing-isogeny).

Localize at a finite set of generators of `I`: torsion kernels and cokernels
vanish, so the given map becomes an isomorphism (module localization and its
exactness, def-weil-pbc-module-localization-away and
lem-weil-pbc-localization-module-exact). Build the glueing datum using these
localized isomorphisms and the canonical comparison maps
(def-weil-pbc-formal-glueing-data). The formal glueing equivalence
(prop-weil-pbc-formal-glueing-equivalence) algebraizes the datum and its map;
comparison of components gives `ψ` and `β`. The localized `ψ` are isomorphisms.
Thus each element of its kernel and cokernel is killed by a power of every
generator. Choose positive exponents `eᵢ` killing that element and use degree
`1 + ∑ eᵢ`: every generating monomial has an exponent at least `eᵢ`, so
this power of `I` kills the element, including for the empty generating set.
Flatness identifies the base-changed
kernel with the kernel of the base-changed map (lem-weil-pbc-flat-tensor-exact);
right exactness gives the analogous cokernel identification
(lem-weil-pbc-tensor-right-exact). For ideal-power torsion modules the map
`x ↦ 1 ⊗ x` is an isomorphism (lem-weil-pbc-torsion-module-flat-base-change-iso).
These composites are the canonical comparison maps specified below.
Finally `β` transports their targets to the kernel and cokernel of `φ'`;
the last two clauses specify these transported comparisons.
-/
theorem exists_map_to_of_torsion_baseChange
    (hflat : (algebraMap R S).Flat) (I : Ideal R) (hI : I.FG)
    (hquot : Function.Bijective
      (Ideal.quotientMap (I.map (algebraMap R S)) (algebraMap R S) Ideal.le_comap_map))
    (P : Type (max u v w)) [AddCommGroup P] [Module R P]
    (Q : Type (max u v w)) [AddCommGroup Q] [Module S Q] [Module R Q]
    [IsScalarTower R S Q]
    (φ' : Q →ₗ[S] S ⊗[R] P)
    (hker : ∀ x : (φ'.restrictScalars R).ker,
      ∃ n : ℕ, ∀ r ∈ I ^ n, r • x = 0)
    (hcoker : ∀ x : _ ⧸ (φ'.restrictScalars R).range,
      ∃ n : ℕ, ∀ r ∈ I ^ n, r • x = 0) :
    ∃ T : ModuleCat.{max u v w} R,
      ∃ (ψ : T →ₗ[R] P) (β : Q ≃ₗ[S] S ⊗[R] T),
        (ψ.baseChange S).comp β.toLinearMap = φ' ∧
        (∀ x : ψ.ker, ∃ n : ℕ, ∀ r ∈ I ^ n, r • x = 0) ∧
        (∀ x : P ⧸ ψ.range, ∃ n : ℕ, ∀ r ∈ I ^ n, r • x = 0) ∧
        (∃ k : ψ.ker ≃ₗ[R] ((ψ.baseChange S).restrictScalars R).ker,
          ∀ x, (k x).val = (1 : S) ⊗ₜ[R] x.val) ∧
        (∃ c : (P ⧸ ψ.range) ≃ₗ[R]
            ((S ⊗[R] P) ⧸ ((ψ.baseChange S).restrictScalars R).range),
          ∀ y : P, c (ψ.range.mkQ y) =
            ((ψ.baseChange S).restrictScalars R).range.mkQ ((1 : S) ⊗ₜ[R] y)) ∧
        (∃ e : ψ.ker ≃ₗ[R] (φ'.restrictScalars R).ker,
          ∀ x, β (e x).val = (1 : S) ⊗ₜ[R] x.val) ∧
        (∃ e : (P ⧸ ψ.range) ≃ₗ[R] (_ ⧸ (φ'.restrictScalars R).range),
          ∀ y : P, e (ψ.range.mkQ y) =
            (φ'.restrictScalars R).range.mkQ ((1 : S) ⊗ₜ[R] y)) := by
  sorry

/-- Part (2) and the comparisons in part (3) of Stacks, Lemma 0ALK;
Lemmas 05EC and 05E9 (blueprint: lem-weil-pbc-formal-glueing-isogeny).

Localize at a finite set of generators of `I`: torsion kernels and cokernels
vanish, so the given map becomes an isomorphism (module localization and its
exactness, def-weil-pbc-module-localization-away and
lem-weil-pbc-localization-module-exact). Build the glueing datum using these
localized isomorphisms and the canonical comparison maps
(def-weil-pbc-formal-glueing-data). The formal glueing equivalence
(prop-weil-pbc-formal-glueing-equivalence) algebraizes the datum and its map;
comparison of components gives `ψ` and `β`. The localized `ψ` are isomorphisms.
Thus each element of its kernel and cokernel is killed by a power of every
generator. Choose positive exponents `eᵢ` killing that element and use degree
`1 + ∑ eᵢ`: every generating monomial has an exponent at least `eᵢ`, so
this power of `I` kills the element, including for the empty generating set.
Flatness identifies the base-changed
kernel with the kernel of the base-changed map (lem-weil-pbc-flat-tensor-exact);
right exactness gives the analogous cokernel identification
(lem-weil-pbc-tensor-right-exact). For ideal-power torsion modules the map
`x ↦ 1 ⊗ x` is an isomorphism (lem-weil-pbc-torsion-module-flat-base-change-iso).
These composites are the canonical comparison maps specified below.
Finally `β` transports their targets to the kernel and cokernel of `φ'`;
the last two clauses specify these transported comparisons.
For part (2), use the inverses of the localized maps in the glueing datum.
-/
theorem exists_map_from_of_torsion_baseChange
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
        (∀ x : T ⧸ ψ.range, ∃ n : ℕ, ∀ r ∈ I ^ n, r • x = 0) ∧
        (∃ k : ψ.ker ≃ₗ[R] ((ψ.baseChange S).restrictScalars R).ker,
          ∀ x, (k x).val = (1 : S) ⊗ₜ[R] x.val) ∧
        (∃ c : (T ⧸ ψ.range) ≃ₗ[R]
            ((S ⊗[R] T) ⧸ ((ψ.baseChange S).restrictScalars R).range),
          ∀ y : T, c (ψ.range.mkQ y) =
            ((ψ.baseChange S).restrictScalars R).range.mkQ ((1 : S) ⊗ₜ[R] y)) ∧
        (∃ e : ψ.ker ≃ₗ[R] (φ'.restrictScalars R).ker,
          ∀ x, (e x).val = (1 : S) ⊗ₜ[R] x.val) ∧
        (∃ e : (T ⧸ ψ.range) ≃ₗ[R] (_ ⧸ (φ'.restrictScalars R).range),
          ∀ y : T, e (ψ.range.mkQ y) =
            (φ'.restrictScalars R).range.mkQ (β ((1 : S) ⊗ₜ[R] y))) := by
  sorry

end FormalGlueing
