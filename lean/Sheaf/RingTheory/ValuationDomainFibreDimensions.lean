/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q49
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Valuation.ValuationRing
public import Mathlib.Topology.Irreducible
public import Mathlib.Topology.KrullDimension
import Sheaf.RingTheory.FiniteTypeDomainDimensionTrdeg
import Sheaf.RingTheory.DimensionAtPointComponents
import Sheaf.AlgebraicGeometry.FibreDimensionBoundedOpenUpstairs
import Sheaf.Paper.QuasiFiniteOverPolynomialAlgebra
import Sheaf.RingTheory.QuasiFiniteFourRings
import WeilConjectures.Mathlib.Topology.KrullDimension
import WeilConjectures.Topology.DimensionSupremumLocalDimensions
import Sheaf.TraceFormula.QuasiFinitePolynomialKernelDimensionDrop

/-!
# Fibre dimensions of a finite type domain over a valuation ring

Source: Stacks Project, Algebra, Tag 00QK
(lemma-finite-type-domain-over-valuation-ring-dim-fibres), including equidimensionality
(blueprint: lem-trf-valuation-domain-fibre-dimensions).
-/

@[expose] public section

set_option autoImplicit false

universe u v

open scoped TensorProduct

namespace ValuationRing

/-- A nonzero closed fibre of a finite type domain containing a valuation ring has the
same Krull dimension as the generic fibre, and every irreducible component of its spectrum
has that dimension. The tensor products carry Mathlib's algebra tensor-product multiplication.

Source: Stacks Project, Algebra, Tag 00QK
(lemma-finite-type-domain-over-valuation-ring-dim-fibres), statement and complete proof
(blueprint: lem-trf-valuation-domain-fibre-dimensions).

Proof plan, following the eight steps of the node:
1. Put `F = D ⊗[A] FractionRing A` and `E = D ⊗[A] IsLocalRing.ResidueField A`.
   By `lem-weil-pbc-generic-fibre-localization-domain-irreducible`, `F` is a nonzero domain
   obtained by localizing `D` at the nonzero elements of `A`. Tensor images of generators
   show both fibres are finite type over their fields. By
   `lem-weil-pbc-finite-type-domain-dimension-trdeg`, `dim F` is a finite integer `d`, equal
   to the transcendence degree of its fraction field. The sole-component case of
   `lem-weil-pbc-dimension-at-point-components` gives local dimension `d` everywhere on
   `Spec F`; use `lem-weil-pbc-spec-topological-krull-dimension-ring` to compare dimensions.
2. Fix a prime `Q` of `E`. The correspondence
   `lem-weil-pbc-fibre-ring-primes-bijection` gives a prime `q` of `D` above the maximal
   ideal of `A`. Its local fibre dimension is a finite integer `n` by
   `lem-weil-pbc-dimension-at-point-components`. The open neighbourhood supplied by
   `lem-weil-pbc-fibre-dimension-bounded-open-upstairs` contains the generic point of the
   domain `D`, where the local fibre dimension is `d`. Thus `d ≤ n`.
3. By `lem-weil-pbc-quasi-finite-over-polynomial-algebra`, choose `g` outside `q` and an
   everywhere quasi-finite finite type map from the polynomial algebra on `n` variables
   to `B = D[g⁻¹]`. Its two fibres `H` and `T` are the away localizations of `F` and `E`
   by `lem-weil-pbc-localization-base-change`. The basic-open identification
   `lem-weil-pbc-spec-localization-away-basic-open` and
   `lem-weil-pbc-dimension-at-point-open-subspace` give local dimension `n` at the prime
   of `T` corresponding to `Q`; in particular `T` is nonzero.
4. Tensor the polynomial map with either field, using
   `lem-weil-pbc-polynomial-scalar-extension`. The maps on `H` and `T` are finite type
   and quasi-finite by `lem-weil-pbc-quasi-finite-four-rings`: every tensor is a finite
   sum of products of images of the two factors. The original generators together with
   the inverse of `g` generate these fibre algebras over their fields.
5. If `d < n`, the generic polynomial map has nonzero kernel: otherwise its variable
   images in the fraction field of `F` are algebraically independent and force
   transcendence degree at least `n` by `def-kun-transcendence-degree`.
6. Choose a nonzero coefficient dividing all coefficients in the valuation ordering.
   Finite induction using total divisibility supplies it, without a rank or discreteness
   assumption. Dividing the kernel polynomial by this coefficient gives coefficients in
   `A` and one coefficient equal to one. The polynomial vanishes in `B`, since `B` embeds
   into its generic fibre by `lem-weil-pbc-generic-fibre-localization-domain-irreducible`.
7. Its reduction is a nonzero polynomial in the kernel of the special-fibre map.
   By `lem-trf-quasi-finite-polynomial-kernel-dimension-drop`, `dim Spec T < n`, contrary
   to the local dimension `n` at the chosen prime: local dimension is at most global
   dimension by `def-kun-topological-dimension-at-point`. Hence `n ≤ d`, and `n = d`.
8. Every point of `Spec E` has local dimension `d`. Apply
   `lem-weil-pbc-dimension-supremum-local-dimensions`, using nonemptiness of `Spec E`,
   and `lem-weil-pbc-spec-topological-krull-dimension-ring` to obtain `dim E = dim F`.
   By `lem-weil-pbc-spec-irreducible-components-minimal-primes`, each component is `V(p)`
   for a minimal prime `p`. It is the unique component through `p`, so
   `lem-weil-pbc-dimension-at-point-components` identifies its dimension with `d`.
-/
theorem finiteType_domain_fibre_dimensions
    (A : Type u) [CommRing A] [IsDomain A] [ValuationRing A]
    (D : Type v) [CommRing D] [IsDomain D] [Algebra A D] [Algebra.FiniteType A D]
    (hAD : Function.Injective (algebraMap A D))
    [Nontrivial (D ⊗[A] IsLocalRing.ResidueField A)] :
    ringKrullDim (D ⊗[A] IsLocalRing.ResidueField A) =
        ringKrullDim (D ⊗[A] FractionRing A) ∧
      ∀ Z : Set (PrimeSpectrum (D ⊗[A] IsLocalRing.ResidueField A)),
        Z ∈ irreducibleComponents (PrimeSpectrum (D ⊗[A] IsLocalRing.ResidueField A)) →
          topologicalKrullDim Z = ringKrullDim (D ⊗[A] FractionRing A) := by
  sorry

end ValuationRing
