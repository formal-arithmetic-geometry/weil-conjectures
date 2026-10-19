/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q66
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Spectrum.Prime.Basic
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Topology.KrullDimension
public import Mathlib.Topology.Irreducible
import WeilConjectures.RingTheory.FiniteTypeDomainDimensionTrdeg
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.BaseChange
import WeilConjectures.RingTheory.DimensionAtPointLocalRingTrdeg
import WeilConjectures.RingTheory.DimensionAtPointComponents
import WeilConjectures.Mathlib.Topology.KrullDimension
import WeilConjectures.AlgebraicGeometry.FibreDimensionBoundedOpenUpstairs

/-!
# Dimension lower bound for components of a finite-type fibre

Source: Stacks Project, `varieties.tex`, Tag 0B2L, lemma-dimension-fibres-locally-algebraic,
(2)(a) (blueprint: lem-zl-finite-type-fibre-component-lower-bound).

The statement is the affine formulation for a rational closed fibre.  Its proof follows the
transcendence-degree computation for the generic fibre and upper semicontinuity of fibre
dimension described in Tag 0B2L.
-/

@[expose] public section

open Set

universe u v w

namespace Algebra

/-- For a finite-type map of finitely generated algebras over a field, every irreducible
component of a rational closed fibre has dimension at least the dimension of the source
minus the dimension of the image algebra (Stacks, Tag 0B2L (2)(a)).

Proof:
1. Set `P = ker φ`, `A = B/P`, `H = C/J`, and `L = Frac(C)`. Since `C` is a
   domain, `P` is prime and `A` embeds in `C`. Put `K = Frac(A)`, embedded in `L`.
   Finite generators descend to `A` and `H`, and generators of `C` over `k` also generate
   it over `A` (def-weil-pbc-finite-type-algebra).
2. By lem-weil-pbc-finite-type-domain-dimension-trdeg and
   lem-kun-transcendence-degree-tower, the two ring dimensions are finite natural numbers
   and their difference `d` is `trdeg_K L`, hence nonnegative.
3. Identify the residue field at `P` with `K`. By
   lem-weil-pbc-generic-fibre-localization-domain-irreducible, the generic fibre
   `K ⊗[A] C` is the localization of `C` at the nonzero elements of `A`, is a nonzero
   domain, and is finite type over `K`. Tensor symmetry identifies it with the `B`-fibre.
4. This localization has fraction field `L`; its local ring and residue field at the zero
   prime are `L`. The field has dimension zero. By
   lem-weil-pbc-dimension-at-point-local-ring-trdeg, the local dimension of the generic
   fibre at its generic point is `trdeg_K L = d`.
5. If `H` is zero there are no components. Otherwise the bijective structure map
   `k → B/m` identifies the residue field at `m` with `k`. The maps `c ⊗ a ↦ a*c̄`
   and `c̄ ↦ c ⊗ 1` identify the rational closed fibre with `H`; the latter map kills
   every generator of `J` (def-weil-pbc-localization-at-prime).
6. By lem-weil-pbc-spec-irreducible-components-minimal-primes write `W = V(q̄)` for
   a minimal prime of `H`. Its inverse image `q` in `C` contracts to `m`. Minimality
   makes `W` the only component through `q̄`, so
   lem-weil-pbc-dimension-at-point-components identifies the local dimension there with
   `dim W`. The fibre homeomorphism preserves local dimensions by matching open
   neighbourhoods and lem-weil-pbc-homeomorphism-krull-dimension.
7. By lem-weil-pbc-fibre-dimension-bounded-open-upstairs, an open neighbourhood of `q`
   bounds every local fibre dimension by `dim W`. By
   lem-weil-pbc-spec-irreducible-closed-subsets-primes, the zero prime is dense in the
   spectrum of the domain `C`, so lies in this neighbourhood. The generic-fibre
   calculation gives `dim C - dim A = d ≤ dim W`.
(blueprint: lem-zl-finite-type-fibre-component-lower-bound)
-/
theorem finiteType_fibre_component_lower_bound
    (k : Type u) [Field k]
    (B : Type v) [CommRing B] [Algebra k B] [Algebra.FiniteType k B]
    (C : Type w) [CommRing C] [Algebra k C] [Algebra.FiniteType k C] [IsDomain C]
    (φ : B →ₐ[k] C)
    (m : Ideal B) (hm : m.IsMaximal)
    (hmk : Function.Bijective (algebraMap k (B ⧸ m))) :
    ∃ dC dA : ℕ,
      ringKrullDim C = (dC : WithBot ℕ∞) ∧
      ringKrullDim (B ⧸ RingHom.ker φ.toRingHom) = (dA : WithBot ℕ∞) ∧
      ∀ W : Set (PrimeSpectrum (C ⧸ Ideal.map φ.toRingHom m)),
        W ∈ irreducibleComponents (PrimeSpectrum (C ⧸ Ideal.map φ.toRingHom m)) →
          ((dC - dA : ℕ) : WithBot ℕ∞) ≤ topologicalKrullDim W := by
  sorry

end Algebra
