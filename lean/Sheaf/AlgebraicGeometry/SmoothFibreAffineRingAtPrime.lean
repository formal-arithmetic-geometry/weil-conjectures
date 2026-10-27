/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q46
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import WeilConjectures.RingTheory.SingularIdeal
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties
import Mathlib.RingTheory.Spectrum.Prime.Topology
import WeilConjectures.AlgebraicGeometry.SpecFieldPointResidueField
import WeilConjectures.AlgebraicGeometry.Sites.EtaleTopologicalInvariance.PropertyC

/-!
# Smoothness of an affine fibre ring at its residue-field kernel prime

Source: Stacks Project, Morphisms, Tag 01V9 (`lemma-smooth-at-point`), the affine
translation in the proof of (2) implies (1).
(blueprint: lem-trf-smooth-fibre-affine-ring-at-prime).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Smoothness near the point over `x` of the scheme fibre gives smoothness at the
corresponding prime of the affine fibre ring.

The affine opens are parametrized by open immersions `iA : Spec A ⟶ X` and
`iR : Spec R ⟶ S`. The commuting square says that the ring map induced by `f`
on these charts is `algebraMap R A`. The condition `hx` says that `q` represents `x`.
With `p = PrimeSpectrum.comap (algebraMap R A) q`, Mathlib's `p.asIdeal.Fiber A`
is `κ(p) ⊗[R] A`, with its usual left-factor `κ(p)`-algebra structure. Tensor
symmetry identifies it with `A ⊗[R] κ(p)` with scalar map `λ ↦ 1 ⊗ λ`.
The prime `PrimeSpectrum.preimageEquivFiber R A p ⟨q, rfl⟩` is, by its definition,
the kernel of the tensor map `λ ⊗ a ↦ κ(algebraMap R A)(λ) * ā` to `κ(q)`.
Thus it is precisely the prime `ker ρ` in the node, transported by tensor symmetry.

Source: Stacks Project, Morphisms, Tag 01V9, proof of (2) implies (1).
(blueprint: lem-trf-smooth-fibre-affine-ring-at-prime).

Proof:
1. Identify the scheme residue fields at `f x` and `x` with `κ(p)` and `κ(q)`
   using lem-weil-pbc-affine-open-stalk-localization and
   lem-weil-pbc-spec-residue-field-identification. The canonical field point
   factors through `iR` by lem-weil-pbc-spec-field-point-residue-field.
   The field maps agree by lem-weil-pbc-spec-map-residue-field-naturality.
2. By lem-weil-pbc-open-fibre-product the inverse image of the chart `Spec A`
   is an open subscheme of the fibre. The chart square, equivalently
   lem-weil-pbc-affine-opens-induced-ring-map-spec-square, and
   lem-weil-pbc-fibre-product-affine-spectra identify it with `Spec (p.Fiber A)`,
   compatibly with both projections. No finite-presentation hypothesis is needed.
3. The tensor residue map respects the balancing relation and its kernel is prime,
   since the target is a field. Its point maps to `q`, hence to `x`. By the
   homeomorphism in def-pc-scheme-fibre it is the unique fibre point `f.asFiber x`.
4. Intersect the given smooth neighbourhood with this chart. Choose a principal
   open containing the kernel prime inside the intersection by
   lem-weil-pbc-spec-localization-away-basic-open. Its element `h` is outside
   the prime, and lem-weil-pbc-principal-localization-open-immersion identifies
   it with `Spec (Localization.Away h)`. By
   lem-weil-pbc-smooth-restrict-open-subschemes the resulting morphism to
   `Spec κ(p)` is smooth, with ring map the localization of the scalar map.
5. By lem-weil-pbc-smooth-ring-map-iff-smooth-affine this localization is a
   smooth `κ(p)`-algebra. This is exactly `Algebra.IsSmoothAtPrime`, the
   existential principal-localization notion of def-weil-pbc-singular-ideal. -/
theorem smooth_fibre_affine_ring_at_prime
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X)
    (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    (iA : Spec (CommRingCat.of A) ⟶ X) (iR : Spec (CommRingCat.of R) ⟶ S)
    [IsOpenImmersion iA] [IsOpenImmersion iR]
    (hsquare : iA ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R A)) ≫ iR)
    (q : PrimeSpectrum A) (hx : iA q = x)
    (hsmooth : ∃ N : (f.fiber (f x)).Opens,
      f.asFiber x ∈ N ∧ Smooth (N.ι ≫ f.fiberToSpecResidueField (f x))) :
    Algebra.IsSmoothAtPrime (PrimeSpectrum.comap (algebraMap R A) q).asIdeal.ResidueField
      (PrimeSpectrum.preimageEquivFiber R A (PrimeSpectrum.comap (algebraMap R A) q)
        ⟨q, rfl⟩) := by
  sorry

end AlgebraicGeometry
