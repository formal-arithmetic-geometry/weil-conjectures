/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.Algebra.Field.ULift
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Scheme
import WeilConjectures.RingTheory.AffineGeometricallyIntegralProjective
import WeilConjectures.RingTheory.LocalUniversalInjectiveResidue

/-!
# Localization intersection over generic fibre primes

Source: Stacks Project, `literature/stacks-project/flat.tex`, Tag 0810, final paragraph
(blueprint: lem-trf-affine-generic-localization-intersection).

## Main declarations

* `AlgebraicGeometry.affineFiberGenericPrime`: inverse image of the fibre zero prime.
* `AlgebraicGeometry.injective_to_pi_affineFiberGenericLocalization`: product injectivity.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v w

open scoped TensorProduct

namespace AlgebraicGeometry

/-- The prime of `B` obtained as the inverse image of the zero prime of the fibre
`p.asIdeal.Fiber B = κ(p) ⊗[R] B`.  The domain hypothesis in the argument supplies the prime proof.

Source: Stacks Project, Tag 0810, final paragraph
(blueprint: lem-trf-affine-generic-localization-intersection). -/
noncomputable def affineFiberGenericPrime
    (R : Type u) [CommRing R]
    (B : Type v) [CommRing B] [Algebra R B]
    (hgeom : ∀ (p : PrimeSpectrum R) (K : Type (max u v w)) [Field K]
      [Algebra p.asIdeal.ResidueField K] [Algebra R K]
      [IsScalarTower R p.asIdeal.ResidueField K],
      IsDomain (K ⊗[R] B))
    (p : PrimeSpectrum R) : PrimeSpectrum B := by
  let K₀ := p.asIdeal.ResidueField
  let K₁ := ULift.{max u v w} K₀
  letI : IsDomain (K₁ ⊗[R] B) := hgeom p K₁
  let e : K₁ ⊗[R] B ≃ₐ[R] K₀ ⊗[R] B :=
    Algebra.TensorProduct.congr ULift.algEquiv (.refl : B ≃ₐ[R] B)
  letI : IsDomain (K₀ ⊗[R] B) := e.toRingEquiv.isDomain_iff.mp inferInstance
  exact PrimeSpectrum.mk
    (Ideal.comap
      (Algebra.TensorProduct.includeRight (R := R) (A := p.asIdeal.ResidueField)
        (B := B)).toRingHom ⊥)
    (Ideal.IsPrime.comap _)

/-- For a flat finitely presented algebra whose fibres remain domains after every
field extension of every residue field, the algebra embeds into the product of the
localizations at the generic primes of its fibres.

Source: Stacks Project, `literature/stacks-project/flat.tex`, Tag 0810, final paragraph;
the local injection is the specialization of Tag 05DH after the base localization
(blueprint: lem-trf-affine-generic-localization-intersection).

Proof:
1. Fix `p`, put `A = R_p`, let `m` be its maximal ideal, and let `C` be `B`
   localized at `R \ p`. By def-weil-pbc-localization-at-prime its reduction is
   `F = p.asIdeal.Fiber B`. This is a nonzero domain. The field map into `F` is
   injective, so the inverse image `q` of zero contracts to `p`. Thus the canonical
   map `C → D = B_q` exists.
2. Apply lem-trf-affine-geometrically-integral-projective (Tag 05FT). By
   def-weil-pbc-projective-module, `B` is a direct summand of a free `R`-module.
   Localize the splitting; a finite-support common-denominator argument identifies
   the localized free module with a free `A`-module. Hence `C` is projective over `A`.
3. The `A`-module `D` is flat: tensor an injection with the flat `R`-algebra `B`,
   then localize at `B \ q`. Localization preserves injectivity by the fraction
   criterion of def-weil-pbc-module-localization. The natural identifications
   `T⁻¹(L ⊗[R] B) = L ⊗[A] D` (def-weil-pbc-module-tensor-product) give the claim.
4. Modulo `m`, the canonical map `C → D` becomes the localization of the domain `F`
   at the images of `B \ q`, all nonzero. The fraction criterion makes it injective.
5. Apply lem-trf-local-universal-injective-residue (Tag 05FQ) to `C → D` using
   steps 2--4. Universal injectivity, tested on `A`, gives injectivity of `C → D`.
6. If `b` vanishes in every `B_q`, it vanishes in every base localization by step 5.
   If `b ≠ 0`, its base annihilator `J` is proper. Choose a maximal ideal `p`
   containing `J` by lem-weil-pbc-proper-ideal-contained-in-maximal. The equation
   `b/1 = 0` supplies `r ∉ p` with `rb = 0`, contradicting `r ∈ J ⊆ p`.
   Thus the product map has zero kernel and is injective. For `R = 0`, also `B = 0`,
   so the empty-product map is injective.

Size convention: the theorem is polymorphic in an independent universe `w` and tests
fields in `Type (max u v w)`. Since `w` is arbitrary, this covers every field-extension
universe while also supplying the size needed by `K ⊗[R] B`. Tensor symmetry identifies
the fibre convention with the node's `B ⊗[R] K` and preserves the inverse-image prime.
-/
theorem injective_to_pi_affineFiberGenericLocalization
    (R : Type u) [CommRing R]
    (B : Type v) [CommRing B] [Algebra R B]
    (hflat : RingHom.Flat (algebraMap R B))
    [Algebra.FinitePresentation R B]
    (hgeom : ∀ (p : PrimeSpectrum R) (K : Type (max u v w)) [Field K]
      [Algebra p.asIdeal.ResidueField K] [Algebra R K]
      [IsScalarTower R p.asIdeal.ResidueField K],
      IsDomain (K ⊗[R] B)) :
    Function.Injective
      (fun b : B => fun p : PrimeSpectrum R =>
        algebraMap B (Localization.AtPrime
          (affineFiberGenericPrime R B hgeom p).asIdeal) b) := by
  sorry

end AlgebraicGeometry
