/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q84
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.TensorProduct.Basic
public import Sheaf.TraceFormula.SchematicallyDenseOpen

import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Sheaf.AlgebraicGeometry.AffineSchematicDensityCriterion

/-!
# Principal-open multiplication data over the generic fibre

Source: Stacks Project, More on Morphisms, Tag 0573,
`lemma-scheme-theoretically-dense-generic-fibre`, proof third paragraph;
Algebra, Tag 0565, `lemma-when-injective-covering`.
(blueprint: lem-trf-generic-open-principal-multiplication-data)
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v w

open scoped TensorProduct

namespace AlgebraicGeometry

/-- A schematically dense generic open has a finite cover by principal opens coming from
functions on the total affine scheme, with injective simultaneous multiplication over the
fraction field. The inverse image defining the generic open is written using the continuous
prime-contraction map of `B → B ⊗[A] K`, the underlying map of the canonical projection.
The finite direct sum is written as the canonically identified finite product. No compactness
of `U` is required, and `m = 0` is allowed.

Source: Stacks Project, More on Morphisms, Tag 0573, proof third paragraph;
Algebra, Tag 0565.
(blueprint: lem-trf-generic-open-principal-multiplication-data)

Proof:
1. Choose finite algebra generators of B over A, using def-weil-pbc-finite-type-algebra.
   By def-weil-pbc-module-tensor-product, tensors are sums of pure tensors, and the same
   generators tensored with 1 generate B tensor_A K over K: write each b as a polynomial
   in these generators and move its coefficients into K. The field K is Noetherian,
   since its only ideals are zero and the unit ideal. Apply
   lem-weil-pbc-finite-type-algebra-noetherian to conclude that B tensor_A K is Noetherian.
2. The single affine chart makes Spec(B tensor_A K) locally Noetherian by pqf-def-locnoeth,
   and it is quasi-compact by lem-weil-pbc-affine-scheme-qcqs. Thus it is Noetherian.
   By lem-weil-pbc-noetherian-open-subscheme-noetherian its open U_K is quasi-compact.
3. By lem-weil-pbc-spec-localization-away-basic-open(i), the D(g) contained in U cover U.
   Prime contraction gives p^{-1}(D(g)) = D(g tensor 1). Pulling back this covering and
   taking a finite subcover of U_K gives m and g. Each selected D(g_i) still lies in U.
   If U_K is empty, the empty subcover with m = 0 is permitted.
4. Apply lem-trf-affine-schematic-density-criterion to B tensor_A K and g_i tensor 1.
   The union in that criterion equals U_K by step 3, so the assumed sheaf injection is
   exactly its schematic-density condition. Its equivalent multiplication condition is
   the injectivity asserted here. For m = 0 both conditions force B tensor_A K to be
   the zero ring, so the empty-family case also holds. -/
theorem generic_open_principal_multiplication_data
    (A : Type u) [CommRing A] [IsDomain A]
    (B : Type v) [CommRing B] [Algebra A B]
    (hB : (algebraMap A B).FiniteType)
    (K : Type w) [Field K] [Algebra A K] [IsFractionRing A K]
    (U : (Spec (.of B)).Opens)
    (hU : SchematicallyDenseOpen (Z := Spec (.of (B ⊗[A] K)))
      (TopologicalSpace.Opens.comap
        ⟨PrimeSpectrum.comap (algebraMap B (B ⊗[A] K)),
          PrimeSpectrum.continuous_comap (algebraMap B (B ⊗[A] K))⟩ U)) :
    ∃ (m : ℕ) (g : Fin m → B),
      (∀ i : Fin m, PrimeSpectrum.basicOpen (g i) ≤ U) ∧
      TopologicalSpace.Opens.comap
        ⟨PrimeSpectrum.comap (algebraMap B (B ⊗[A] K)),
          PrimeSpectrum.continuous_comap (algebraMap B (B ⊗[A] K))⟩ U =
        ⨆ i : Fin m, PrimeSpectrum.basicOpen (g i ⊗ₜ[A] (1 : K)) ∧
      Function.Injective (fun b : B ⊗[A] K ↦
        fun i : Fin m ↦ (g i ⊗ₜ[A] (1 : K)) * b) := by
  sorry

end AlgebraicGeometry
