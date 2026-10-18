/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q27
-/
module

public import Mathlib.RingTheory.Localization.Away.Basic
public import Sheaf.TraceFormula.SchematicallyDenseOpen

import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Affine criterion for schematic density of finitely many principal opens

Source: Stacks Project, Algebra, Tag 0565 (`lemma-when-injective-covering`), with M = A;
Morphisms, Tags 056C (`example-scheme-theoretic-closure`) and 01RE
(`lemma-characterize-scheme-theoretically-dense`).
(blueprint: lem-trf-affine-schematic-density-criterion).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

namespace AlgebraicGeometry

/-- For finitely many elements of a ring, injectivity into their localizations is equivalent
both to injectivity of multiplication by their tuple and to schematic density of the union
of their principal opens. The finite direct sums are written as finite products using their
canonical coordinate identification. `SchematicallyDenseOpen` asserts injectivity of
`𝒪_Spec(A) → j_*𝒪_U` on every open, for the canonical open immersion of this union.

Source: Stacks Project, Algebra, Tag 0565; Morphisms, Tags 056C and 01RE.
(blueprint: lem-trf-affine-schematic-density-criterion).

Proof:
1. The fraction relation of def-weil-ring-localization-away identifies the kernel of the
   localization tuple with the a such that f_i ^ e_i * a = 0 for some e_i ≥ 1 for each i.
   Taking all e_i = 1 shows that injectivity of localization implies injectivity of the
   multiplication tuple; zero kernel is equivalent to injectivity by taking differences.
2. Conversely, assuming the multiplication tuple injective, induct strongly on the sum of
   e_i - 1. The zero case is the assumed zero-kernel assertion. Choose j with e_j > 1 and
   apply induction to f_j * a with its j-th exponent decreased by one. This gives f_j * a = 0.
   Replace the j-th exponent of a by one and apply induction again. The empty family has
   sum zero, and both maps then have zero target.
3. By def-weil-affine-spectrum the global sections of Spec A are A; by
   lem-weil-pbc-affine-open-section-vanishing-prime(b), sections on D(f_i) are A[1/f_i],
   compatibly with restriction. By def-weil-open-immersion and sheaf uniqueness on this
   cover of U, restriction to U has the same kernel as the localization tuple. Injectivity
   of the sheaf restriction therefore implies injectivity of the localization tuple.
4. Assuming the latter injective, the multiplication tuple is injective. On any A[1/g],
   if every f_i * (a/g^r) vanishes, choose exponents k_i with g^k_i * f_i * a = 0.
   A common maximum k (zero for the empty family) gives g^k * a = 0 by tuple injectivity.
   Thus the multiplication tuple on A[1/g] is injective, and steps 1--2 give injectivity
   into the corresponding localizations of A[1/g].
5. By lem-weil-pbc-affine-open-section-vanishing-prime, these localizations compute sections
   on D(g) ∩ D(f_i). Hence restriction from D(g) to D(g) ∩ U is injective. The basis in
   lem-weil-pbc-spec-localization-away-basic-open(i) and sheaf uniqueness extend this to
   every open of Spec A, giving the asserted sheaf injectivity. For the empty family the
   hypothesis forces A to be the zero ring, so the argument still applies. -/
theorem affine_schematic_density_criterion (A : Type u) [CommRing A]
    (n : ℕ) (f : Fin n → A) :
    (Function.Injective (fun a : A ↦ fun i : Fin n ↦
        algebraMap A (Localization.Away (f i)) a) ↔
      Function.Injective (fun a : A ↦ fun i : Fin n ↦ f i * a)) ∧
    (Function.Injective (fun a : A ↦ fun i : Fin n ↦
        algebraMap A (Localization.Away (f i)) a) ↔
      SchematicallyDenseOpen (Z := Spec (.of A)) (⨆ i : Fin n, PrimeSpectrum.basicOpen (f i))) := by
  sorry

end AlgebraicGeometry
