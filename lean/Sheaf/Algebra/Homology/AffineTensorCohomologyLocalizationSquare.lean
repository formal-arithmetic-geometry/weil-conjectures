/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import Sheaf.Algebra.Homology.RingTensorCohomology
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.TensorProduct.Basic

import Sheaf.Algebra.Homology.DerivedTensorLocalizationCohomology

import Sheaf.Algebra.Homology.AffineTensorLocalizationFlat

import Mathlib.RingTheory.Localization.BaseChange

import Mathlib.Algebra.Module.LocalizedModule.Exact

/-! # Global-to-local tensor cohomology component isomorphisms

Source: Stacks Project, Tags 0DJ8, 00DL and 00CS.
(blueprint: lem-pc-affine-tensor-cohomology-localization-square). -/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory
open scoped TensorProduct

namespace RingTensorCohomology

/-- The global-to-local cohomology square for prescribed tensor-algebra lifts.
Source: Stacks Project, perfect.tex, Tag 0DJ8, affine displayed localization identity.
(blueprint: lem-pc-affine-tensor-cohomology-localization-square)

Proof: use the functorial A-K-flat resolution P of M and its localization J(P).
The balanced base-derived tensor cohomology models retain the A tensor_R B action.
Apply derivedTensor_localization_cohomology to these models. Its naturality equations
give the first naturality equation for the source identifications alpha.
Its comparison equation identifies
both composites with the localized augmentation on the K-flat comparison span.
For beta, localization is exact, hence commutes with homology. Tensor associativity
identifies the extension of J(P) to D with that of P to D. The localized resolution
augmentation is a quasi-isomorphism from an Aq-K-flat complex; comparing it with the
chosen functorial Aq-K-flat resolution gives the natural target identification.
Transport these maps along eS, eT, eSl, eTl. Their generator equations make them
linear over both tensor factors, hence over the tensor algebras. The equations on
f and hB identify all coefficient maps. The naturality and comparison equations
survive this transport and give the asserted componentwise equality.
The target identifications satisfy the second
naturality equation since every tensor and resolution comparison is natural in M.
This statement concerns only the commuting global-to-local square; it does not
identify the local target after coefficient extension with ordinary D-cohomology.
Zero complexes and identity localizations use the same maps; if no prime exists,
there is no instance of the assertion to check. -/
theorem affineTensorCohomology_localization_square
    (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (i : ℤ)
    (S T : CochainComplex (ModuleCat.{u} A) ℤ ⥤ ModuleCat.{u} (A ⊗[R] B))
      (eS : S ⋙ ModuleCat.restrictScalars Algebra.TensorProduct.includeRight.toRingHom ≅
        source R A B i)
      (eT : T ⋙ ModuleCat.restrictScalars Algebra.TensorProduct.includeRight.toRingHom ≅
        target R A B i)
      (c : S ⟶ T)
    (hS : (∀ (M : CochainComplex (ModuleCat.{u} A) ℤ) (a : A) (x : S.obj M),
        eS.hom.app M ((Algebra.TensorProduct.includeLeft (S := R) a : A ⊗[R] B) • x) =
          (source R A B i).map (a • 𝟙 M) (eS.hom.app M x)))
    (hT : (∀ (M : CochainComplex (ModuleCat.{u} A) ℤ) (a : A) (x : T.obj M),
        eT.hom.app M ((Algebra.TensorProduct.includeLeft (S := R) a : A ⊗[R] B) • x) =
          (target R A B i).map (a • 𝟙 M) (eT.hom.app M x)))
    (hc : Functor.whiskerRight c
          (ModuleCat.restrictScalars Algebra.TensorProduct.includeRight.toRingHom) ≫ eT.hom =
        eS.hom ≫ comparison R A B i)
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
    (Sl Tl : CochainComplex (ModuleCat.{u} Aq) ℤ ⥤
            ModuleCat.{u} (Aq ⊗[Rp] Bp))
          (eSl : Sl ⋙
            ModuleCat.restrictScalars Algebra.TensorProduct.includeRight.toRingHom ≅
            source Rp Aq Bp i)
          (eTl : Tl ⋙
            ModuleCat.restrictScalars Algebra.TensorProduct.includeRight.toRingHom ≅
            target Rp Aq Bp i)
          (cl : Sl ⟶ Tl)
    (hSl : (∀ (M : CochainComplex (ModuleCat.{u} Aq) ℤ) (a : Aq) (x : Sl.obj M),
            eSl.hom.app M ((Algebra.TensorProduct.includeLeft (S := Rp) a : Aq ⊗[Rp] Bp) • x) =
              (source Rp Aq Bp i).map (a • 𝟙 M) (eSl.hom.app M x)))
    (hTl : (∀ (M : CochainComplex (ModuleCat.{u} Aq) ℤ) (a : Aq) (x : Tl.obj M),
            eTl.hom.app M ((Algebra.TensorProduct.includeLeft (S := Rp) a : Aq ⊗[Rp] Bp) • x) =
              (target Rp Aq Bp i).map (a • 𝟙 M) (eTl.hom.app M x)))
    (hcl : Functor.whiskerRight cl
              (ModuleCat.restrictScalars Algebra.TensorProduct.includeRight.toRingHom) ≫
              eTl.hom = eSl.hom ≫ comparison Rp Aq Bp i)
    :
    ∃ (alpha : ∀ M : CochainComplex (ModuleCat.{u} A) ℤ,
        (ModuleCat.extendScalars (algebraMap (A ⊗[R] B) D)).obj (S.obj M) ≅
          (ModuleCat.extendScalars f).obj (Sl.obj ((extend A Aq).obj M)))
      (beta : ∀ M : CochainComplex (ModuleCat.{u} A) ℤ,
        (ModuleCat.extendScalars (algebraMap (A ⊗[R] B) D)).obj (T.obj M) ≅
          (ModuleCat.extendScalars f).obj (Tl.obj ((extend A Aq).obj M))),
      (∀ (M N : CochainComplex (ModuleCat.{u} A) ℤ) (g : M ⟶ N),
        (ModuleCat.extendScalars (algebraMap (A ⊗[R] B) D)).map (S.map g) ≫
            (alpha N).hom =
          (alpha M).hom ≫ (ModuleCat.extendScalars f).map
            (Sl.map ((extend A Aq).map g))) ∧
      (∀ (M N : CochainComplex (ModuleCat.{u} A) ℤ) (g : M ⟶ N),
        (ModuleCat.extendScalars (algebraMap (A ⊗[R] B) D)).map (T.map g) ≫
            (beta N).hom =
          (beta M).hom ≫ (ModuleCat.extendScalars f).map
            (Tl.map ((extend A Aq).map g))) ∧
      (∀ M : CochainComplex (ModuleCat.{u} A) ℤ,
        (ModuleCat.extendScalars (algebraMap (A ⊗[R] B) D)).map (c.app M) ≫
            (beta M).hom =
          (alpha M).hom ≫ (ModuleCat.extendScalars f).map
            (cl.app ((extend A Aq).obj M))) := by
  sorry

end RingTensorCohomology
