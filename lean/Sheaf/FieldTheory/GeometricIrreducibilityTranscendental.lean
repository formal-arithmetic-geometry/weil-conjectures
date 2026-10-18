/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q85
-/
module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import Mathlib.FieldTheory.RatFunc.Basic
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Topology.Irreducible
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Geometric irreducibility and transcendental field extensions

Source: Stacks Project, Algebra, Tag 0G31
(`lemma-geometrically-irreducible-base-change-transcendental`), with the forward
implication iterated over a finite algebraically independent family.
(blueprint: lem-zl-geometric-irreducibility-transcendental).
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace AlgebraicGeometry

/-- Geometric irreducibility ascends after adjoining the same finite algebraically
independent family to the two fields, and descends after adjoining one indeterminate.
The finite family lives in an arbitrary common extension `Ω`. Its generated intermediate
fields are `k(t₁, …, tᵣ)` and `K(t₁, …, tᵣ)`; their displayed map is the inclusion, with
scalar restriction identifying the two copies of the common ambient field. In the
converse, the rational-function map applies `algebraMap k K` to coefficients and fixes
its indeterminate. No separability, finite generation or positive cardinality is assumed.

Source: Stacks Project, Algebra, Tag 0G31
(`lemma-geometrically-irreducible-base-change-transcendental`).
(blueprint: lem-zl-geometric-irreducibility-transcendental).

Proof (the node's eight steps):
1. The affine fibre-product formula identifies each field base change of `Spec L` with
   `Spec (L ⊗[F] F')`. Thus geometric irreducibility means that all these tensor spectra
   are nonempty and irreducible. Evaluation at a transcendental element identifies the
   formal rational-function field with the field it generates.
2. Put `R = K ⊗[k] k(t)` and `S₀ = k[T] ∖ {0}`. Explicitly identify `R` with
   `S₀⁻¹K[T]`, by sending `a ⊗ f(t)/g(t)` to `af(T)/g(T)` and sending `h(T)/g(T)`
   back to the sum of `hᵢ ⊗ tⁱ/g(t)`. Inverting the remaining nonzero polynomials
   gives `K(t)`. Tensor balancing and the fraction relation verify the inverse maps.
3. Given any field `F/k(t)`, put `A = K ⊗[k] F` and `B = K(t) ⊗[k(t)] F`.
   The spectrum of `A` is irreducible by the hypothesis. Localization commutes with
   base change, so `A ⊗[R] K(t)` is a localization of `A`; the pure-tensor maps
   `(a ⊗ f) ⊗ v ↦ av ⊗ f` and `v ⊗ f ↦ (1 ⊗ f) ⊗ v` identify it with `B`.
   Nonzero vector spaces over `k(t)` have nonzero tensor product, so `B` is nonzero.
4. The unique minimal prime `p` of `A` is contained in every prime. A prime of the
   nonzero localization `B` contracts to a prime disjoint from the denominator set,
   so `p` is also disjoint from that set. The localization-spectrum embedding has
   image containing `p`, whose closure is all of `Spec A`; every relatively closed
   subset of the image containing `p` is the whole image. Its closed-cover criterion
   proves that `Spec B` is nonempty and irreducible, establishing one-variable ascent.
5. Induct over the finite family. The empty family is the initial extension. Each next
   variable is transcendental over the preceding generated field: clear polynomial
   denominators in a hypothetical relation to contradict algebraic independence.
   Apply one-variable ascent at each step.
6. For descent fix `k'/k`. Write `C = K ⊗[k] k'`, `D = K(t) ⊗[k] k'` and
   `E = k(t) ⊗[k] k'`. The same fraction calculation identifies `E` with
   `S₀⁻¹k'[T]`, which injects into `k'(t)` because every denominator is nonzero.
7. Flatness of vector spaces and tensor exactness give injections `C → D` and
   `D ≃ K(t) ⊗[k(t)] E → K(t) ⊗[k(t)] k'(t)`. The second isomorphism sends
   `v ⊗ (w ⊗ a)` to `vw ⊗ a`, with inverse `v ⊗ a ↦ v ⊗ (1 ⊗ a)`.
   Their composite sends `a ⊗ b` to `a ⊗ b`, including for inseparable extensions.
8. The last tensor spectrum is irreducible by the descent hypothesis. For the injection
   from `C`, minimal-prime lifting and the dense-range criterion give a dense map to
   `Spec C`. Pull back a two-closed-set cover; irreducibility of the source and density
   make one closed set all of `Spec C`. The source also supplies nonemptiness. This
   holds for every `k'/k`, proving geometric irreducibility of `K/k`.
-/
theorem geometricallyIrreducible_transcendental_extension
    {k K : Type u} [Field k] [Field K] [Algebra k K] :
    (GeometricallyIrreducible (Spec.map (CommRingCat.ofHom (algebraMap k K))) →
      ∀ (Ω : Type (max u v)) [Field Ω] [Algebra k Ω] [Algebra K Ω] [IsScalarTower k K Ω]
        (r : ℕ) (t : Fin r → Ω), AlgebraicIndependent K t →
        GeometricallyIrreducible (Spec.map (CommRingCat.ofHom
          (IntermediateField.inclusion
            (IntermediateField.adjoin_le_iff.mpr
              (IntermediateField.subset_adjoin K (Set.range t))) :
            IntermediateField.adjoin k (Set.range t) →ₐ[k]
              (IntermediateField.adjoin K (Set.range t)).restrictScalars k).toRingHom))) ∧
    (GeometricallyIrreducible (Spec.map (CommRingCat.ofHom
        (RatFunc.mapRingHom (Polynomial.mapRingHom (algebraMap k K))
          (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
            (Polynomial.map_injective _ (algebraMap k K).injective))))) →
      GeometricallyIrreducible (Spec.map (CommRingCat.ofHom (algebraMap k K)))) := by
  sorry

end AlgebraicGeometry
