/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Jacobson.Ideal
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Spectrum.Maximal.Basic
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# A common denominator lies in Jacobson radicals

Source: Stacks Project, Varieties, Lemma 33.37.8 (Tag 09N5)
(blueprint: lem-sc-jacobson-denominator-function-field).
-/

@[expose] public section

universe u v w t

namespace RingTheory

/-- Source: Stacks Project, Varieties, Lemma 33.37.8 (Tag 09N5).
For a domain `A` with fraction field `K` and a finite family of Noetherian one-dimensional
semilocal domains `B i` in `K` with fraction field `K`, if each canonical multiplication map
`A ⊗[ℤ] B i → K` is surjective, then a nonzero element of `A` has inverse in the Jacobson
radical of every `B i`.

Proof (Stacks Tag 09N5):
1. Replace each `B i` by its integral closure `B' i` in `K`. The tensor map remains
   surjective since its image contains the old image. By
   `lem-sc-semilocal-dim-one-conductor`, each `B' i` is semilocal Dedekind. If a nonzero
   `x : A` has inverse in their radicals, that conductor lemma with `y = 1` gives positive
   exponents `n i` with `x ^ (-n i)` in `B i`. Replace `x` by the power whose exponent is
   the product of these finitely many exponents. Its inverse then belongs to every `B i`
   and remains in every radical of `B' i`. For a maximal ideal `m` of `B i`, integral
   lying-over (`lem-weil-pbc-integral-injective-lying-over`) gives a prime above `m` in
   `B' i`. A maximal ideal containing that prime contracts to `m`, so the inverse lies
   in `m`. This descends radical membership to `B i`.
2. By `lem-sc-semilocal-dedekind-dvr-reduction`, replace every semilocal Dedekind ring
   by its finitely many localizations at maximal ideals. These are DVRs with fraction
   field `K`, their tensor maps remain surjective, and membership in all their maximal
   ideals is equivalent to membership in the original Jacobson radical.
3. For one DVR, `lem-sc-dvr-tensor-surjective-negative-valuation` gives a nonzero element
   of `A` with negative valuation: otherwise `A` lies in the DVR and the tensor map
   cannot surject onto `K`. Induct on the finite family of valuations. Choose nonzero
   `x` negative at all but the last valuation. If it is negative there too, finish.
   Otherwise choose nonzero `y` negative at the last valuation by the base case.
   Using `lem-sc-dvr-valuation-arithmetic`, replace `x` by a sufficiently large positive
   power so its valuations at all earlier places are smaller than those of `y`.
   The unequal-value sum rule makes `x + y` negative at every place and nonzero.
   Its inverse has positive valuation, hence lies in every maximal ideal. For the empty
   family take `1 : A`.
(blueprint: lem-sc-jacobson-denominator-function-field) -/
theorem exists_inv_mem_jacobson_of_tensor_surjective
    {A : Type u} {K : Type v} [CommRing A] [IsDomain A] [Field K]
    [Algebra A K] [IsFractionRing A K]
    {ι : Type w} [Finite ι]
    (B : ι → Type t) [∀ i, CommRing (B i)] [∀ i, IsDomain (B i)]
    [∀ i, IsNoetherianRing (B i)] [∀ i, Finite (MaximalSpectrum (B i))]
    (hdim : ∀ i, ringKrullDim (B i) = 1)
    [∀ i, Algebra (B i) K] [∀ i, IsFractionRing (B i) K]
    (hsurj : ∀ i, Function.Surjective
      (Algebra.TensorProduct.productMap
        (IsScalarTower.toAlgHom ℤ A K) (IsScalarTower.toAlgHom ℤ (B i) K))) :
    ∃ f : A, f ≠ 0 ∧ ∀ i, ∃ b : B i,
      b ∈ (Ideal.jacobson (⊥ : Ideal (B i)) : Set (B i)) ∧
        algebraMap (B i) K b = (algebraMap A K f)⁻¹ := by
  sorry

end RingTheory
