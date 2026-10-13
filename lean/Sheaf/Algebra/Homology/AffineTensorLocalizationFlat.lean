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
  -- Work over R first; the localized base is removed by a canonical equivalence.
  let C := A ⊗[R] B
  let T₀ := Aq ⊗[R] B
  let T₁ := Aq ⊗[R] Bp
  let e := IsLocalization.algebraTensorEquiv
    (q'.asIdeal.comap (algebraMap R C)).primeCompl Rp Aq Bp
  let g : T₁ →+* D := f.comp e.symm.toRingHom
  let j : T₀ →ₐ[R] T₁ := Algebra.TensorProduct.map (AlgHom.id R Aq)
    (IsScalarTower.toAlgHom R B Bp)
  let i : C →ₐ[R] T₀ := Algebra.TensorProduct.map
    (IsScalarTower.toAlgHom R A Aq) (AlgHom.id R B)
  let : Algebra C T₀ := i.toRingHom.toAlgebra
  let : Algebra T₀ T₁ := j.toRingHom.toAlgebra
  let : Algebra T₁ D := g.toAlgebra
  let : Algebra T₀ D := (g.comp j.toRingHom).toAlgebra
  have : IsScalarTower T₀ T₁ D := .of_algebraMap_eq' rfl
  have : IsScalarTower Aq T₀ T₁ := .of_algebraMap_eq fun a ↦ by
    simp [j, T₀, T₁, Algebra.TensorProduct.algebraMap_apply,
      Algebra.TensorProduct.map_tmul, RingHom.algebraMap_toAlgebra]
  have : IsScalarTower A C T₀ := .of_algebraMap_eq fun a ↦ by
    simp [i, C, T₀, Algebra.TensorProduct.algebraMap_apply,
      Algebra.TensorProduct.map_tmul, RingHom.algebraMap_toAlgebra]
  -- The prescribed factor maps identify the composite with the given C-action.
  have : IsScalarTower C T₀ D := by
    apply IsScalarTower.of_algebraMap_eq
    have hg_tmul (a : Aq) (b : Bp) : g (a ⊗ₜ[R] b) = f (a ⊗ₜ[Rp] b) := rfl
    intro c
    induction c using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      change algebraMap C D (a ⊗ₜ[R] b) = g (j (i (a ⊗ₜ[R] b)))
      rw [show i (a ⊗ₜ[R] b) = algebraMap A Aq a ⊗ₜ[R] b by rfl,
        show j (algebraMap A Aq a ⊗ₜ[R] b) =
          algebraMap A Aq a ⊗ₜ[R] algebraMap B Bp b by rfl, hg_tmul]
      rw [show algebraMap A Aq a ⊗ₜ[Rp] algebraMap B Bp b =
        Algebra.TensorProduct.includeLeft (S := Rp) (algebraMap A Aq a) *
          Algebra.TensorProduct.includeRight (algebraMap B Bp b) by
            simp [Algebra.TensorProduct.includeLeft_apply,
              Algebra.TensorProduct.tmul_mul_tmul]]
      rw [map_mul, _hfA, _hfB, ← IsScalarTower.algebraMap_apply A Aq D,
        ← IsScalarTower.algebraMap_apply B Bp D, _hB,
        IsScalarTower.algebraMap_apply A C D, ← map_mul]
      simp [C, Algebra.TensorProduct.algebraMap_apply,
        Algebra.TensorProduct.tmul_mul_tmul]
    | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
  -- Localize the first factor, then view the stalk as a further localization.
  have : IsLocalization
      (Algebra.algebraMapSubmonoid C
        (q'.asIdeal.comap (algebraMap A C)).primeCompl) T₀ :=
    IsLocalization.tensorProduct_tensorProduct R B
      (q'.asIdeal.comap (algebraMap A C)).primeCompl Aq (by
        ext b
        change algebraMap A Aq 1 ⊗ₜ[R] b = 1 ⊗ₜ[R] b
        rw [map_one])
  have hle : Algebra.algebraMapSubmonoid C
      (q'.asIdeal.comap (algebraMap A C)).primeCompl ≤ q'.asIdeal.primeCompl := by
    rintro _ ⟨a, ha, rfl⟩
    exact ha
  have : IsLocalization
      (q'.asIdeal.primeCompl.map (algebraMap C T₀)) D :=
    IsLocalization.isLocalization_of_submonoid_le T₀ D _ _ hle
  have hflat₀ : Module.Flat T₀ D :=
    IsLocalization.flat D (q'.asIdeal.primeCompl.map (algebraMap C T₀))
  -- Localizing the second factor preserves flatness over the coefficient ring.
  have : IsLocalization
      ((q'.asIdeal.comap Algebra.TensorProduct.includeRight.toRingHom).primeCompl.map
        (Algebra.TensorProduct.includeRight (R := R) (A := Aq))) T₁ :=
    IsLocalization.tensorProduct_tensorProduct_right R Aq
      (q'.asIdeal.comap Algebra.TensorProduct.includeRight.toRingHom).primeCompl Bp (by
        ext b
        simp [j, T₀, T₁, Algebra.TensorProduct.map_tmul,
          RingHom.algebraMap_toAlgebra])
  have hflat₁ : Module.Flat T₁ D :=
    (Module.flat_iff_of_isLocalization T₁
      ((q'.asIdeal.comap Algebra.TensorProduct.includeRight.toRingHom).primeCompl.map
        (Algebra.TensorProduct.includeRight (R := R) (A := Aq))) D).mpr hflat₀
  have hg : g.Flat := (RingHom.flat_algebraMap_iff (R := T₁) (S := D)).mpr hflat₁
  exact (RingHom.Flat.comp_iff_of_bijective_right e.symm.toRingEquiv.bijective).mp hg

end RingTensorCohomology
