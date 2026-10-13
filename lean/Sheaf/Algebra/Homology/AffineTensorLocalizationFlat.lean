/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.TensorProduct.Basic

import Mathlib.RingTheory.Localization.BaseChange

import Mathlib.RingTheory.Localization.LocalizationLocalization

/-! # Flatness of the local affine tensor coefficient map

Source: Stacks Project, Tags 0DJ8, 00DL and 00CS.
(blueprint: lem-pc-affine-tensor-localization-flat). -/

@[expose] public section

set_option autoImplicit false

universe u

open scoped TensorProduct

namespace RingTensorCohomology

/-- The coefficient map from the localized tensor algebra to the tensor stalk is flat.
Source: Stacks Project, algebra.tex, Tags 00DL and 00CS; perfect.tex, Tag 0DJ8.
(blueprint: lem-pc-affine-tensor-localization-flat)

Proof: put C = A tensor_R B. First localize C by the multiplicative set generated
by a tensor 1 for a outside the contraction to A and 1 tensor b for b outside
the contraction to B. The tensor-localization universal property identifies this
ring with Aq tensor_R Bp. All elements of R outside its contracted prime already
become units in both factors, so changing the tensor base from R to Rp identifies
this ring with Aq tensor_Rp Bp. Every inverted element is outside qprime. The
universal property of successive localization therefore identifies D with the
localization of this ring at the image of C minus qprime. The specified equations
on f, hB and the scalar towers identify its structure map with f: they agree on
both tensor factors, and extension to the local factors is unique. Localization
is flat (equivalently its scalar extension on modules is exact), so f is flat.
Identity localizations give the identity flat map. Empty prime spectra have no
qprime and impose no assertion; no injectivity of localization maps is used. -/
theorem affineTensorLocalization_flat
    (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B]
    (q' : PrimeSpectrum (A ⊗[R] B))
        (Rp Aq Bp D : Type u) [CommRing Rp] [CommRing Aq] [CommRing Bp] [CommRing D]
        [Algebra R Rp] [Algebra A Aq] [Algebra B Bp] [Algebra (A ⊗[R] B) D]
        [IsLocalization.AtPrime Rp (q'.asIdeal.comap (algebraMap R (A ⊗[R] B)))]
        [IsLocalization.AtPrime Aq (q'.asIdeal.comap (algebraMap A (A ⊗[R] B)))]
        [IsLocalization.AtPrime Bp (q'.asIdeal.comap
          Algebra.TensorProduct.includeRight.toRingHom)]
        [IsLocalization.AtPrime D q'.asIdeal]
        [Algebra R Aq] [Algebra R Bp] [Algebra Rp Aq] [Algebra Rp Bp]
        [IsScalarTower R A Aq] [IsScalarTower R B Bp]
        [IsScalarTower R Rp Aq] [IsScalarTower R Rp Bp]
        [Algebra A D] [Algebra B D] [Algebra Aq D] [Algebra Bp D]
        [IsScalarTower A (A ⊗[R] B) D]
        [IsScalarTower A Aq D]
        (_hB : ∀ b : B, algebraMap B D b =
          algebraMap (A ⊗[R] B) D (Algebra.TensorProduct.includeRight b))
        [IsScalarTower B Bp D]
        (f : (Aq ⊗[Rp] Bp) →+* D)
        (_hfA : ∀ a : Aq,
          f (Algebra.TensorProduct.includeLeft (S := Rp) a : Aq ⊗[Rp] Bp) = algebraMap Aq D a)
        (_hfB : ∀ b : Bp, f (Algebra.TensorProduct.includeRight b) = algebraMap Bp D b)
    : f.Flat := by
  sorry

end RingTensorCohomology
