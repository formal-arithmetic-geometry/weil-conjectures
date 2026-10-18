/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q111
-/
module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.DirectSum.Decomposition
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
public import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Flat.Equalizer
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.Noetherian.Basic
import WeilConjectures.Mathlib.RingTheory.Flat.Equalizer

/-!
# Finite presentation of a finite flat graded module over a local polynomial ring

Source: Stacks Project, Tag 053C, `lemma-flat-graded-finite-type-finite-presentation-module`,
statement and proof in `literature/stacks-project/more-algebra.tex`, lines 5856--5909
(blueprint: lem-trf-local-graded-flat-module-finite-presentation).
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace WeilConjectures

/-- A finite graded module over a positively weighted polynomial ring over a local ring is
finitely presented if it is flat over the coefficient ring.

Source: Stacks Project, Tag 053C, `lemma-flat-graded-finite-type-finite-presentation-module`,
statement at lines 5856--5870 and proof at lines 5871--5909
(blueprint: lem-trf-local-graded-flat-module-finite-presentation).

The integer-weighted homogeneous submodules of Mathlib are exactly the spans of the monomials
of the indicated weighted degree. Positive weights make all negative-degree pieces zero.
`Ldeg` is an internal direct-sum decomposition by coefficient-ring submodules, with the stated
compatibility with homogeneous scalar multiplication.

Proof:
1. Decompose a finite generating family into its finitely many homogeneous components, giving
   homogeneous generators m_i of degrees d_i and a graded surjection from F = direct sum P(-d_i)
   onto L, with kernel K. In each degree d the sequence 0 → K_d → F_d → L_d → 0 is exact.
   Positivity of the weights makes every P_(d-d_i) finite free, using the finitely many monomials
   of that degree. The degree projection splits the inclusion L_d → L, so
   `lem-weil-pbc-flat-module-retract` makes L_d flat. Since F_d is flat as well,
   `lem-weil-pbc-flat-ses-kernel-flat` makes K_d flat.
2. The products of the m_i with monomials of complementary degree generate L_d over R, so L_d
   is finite. By `lem-weil-pbc-finite-flat-local-free`, it is finite free. The surjection
   F_d → L_d therefore splits, making K_d a retract of the finite free R-module F_d and hence
   finite. Together with step 1, `lem-weil-pbc-finite-flat-local-free` makes K_d finite free.
3. Let κ be the residue field. Tensoring the degreewise exact sequences with κ preserves
   exactness by `lem-weil-pbc-flat-quotient-tensor-injective`. The ring κ[x_1,...,x_n] is
   Noetherian by `lem-weil-pbc-finite-type-algebra-noetherian`. Consequently the relation module
   K tensor κ, a submodule of the finite free module F tensor κ, is finite by
   `lem-weil-pbc-noetherian-submodule-finite`. Choose homogeneous generators and homogeneous
   lifts k_j in K, with degrees e_j.
4. In each degree d the map from the direct sum of P_(d-e_j) to K_d becomes surjective modulo
   the maximal ideal. Its cokernel is a finite R-module by step 2. Apply
   `lem-weil-pbc-nakayama-local-generators` to obtain surjectivity over R. Thus the finitely
   many k_j generate K over P; the finite free presentation F → L and this finite relation
   family give `def-sc-finitely-presented-module`.
-/
theorem local_graded_flat_module_finite_presentation
    {R : Type u} [CommRing R] [IsLocalRing R]
    (n : ℕ) (ω : Fin n → ℕ) (hω : ∀ i : Fin n, 0 < ω i)
    {L : Type v} [AddCommGroup L] [Module (MvPolynomial (Fin n) R) L] [Module R L]
    [IsScalarTower R (MvPolynomial (Fin n) R) L]
    (Ldeg : ℤ → Submodule R L) (hLinternal : DirectSum.IsInternal Ldeg)
    (hgraded : ∀ (e d : ℤ) (p : MvPolynomial (Fin n) R) (x : L),
      p ∈ MvPolynomial.weightedHomogeneousSubmodule R (fun i : Fin n ↦ (ω i : ℤ)) e →
      x ∈ Ldeg d → p • x ∈ Ldeg (e + d))
    [Module.Finite (MvPolynomial (Fin n) R) L] [Module.Flat R L] :
    Module.FinitePresentation (MvPolynomial (Fin n) R) L := by
  sorry

end WeilConjectures
