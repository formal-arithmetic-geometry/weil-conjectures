/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R3
-/
module

public import Sheaf.Algebra.Homology.RingTensorCohomology
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
import Sheaf.Algebra.Homology.AffineTensorCohomologyLocalizationSquare
import Sheaf.Algebra.Homology.AffineTensorLocalizationFlat
import Sheaf.Algebra.Homology.AffineTensorTargetFlatExtension

/-! # Affine tensor cohomology: localization isomorphisms

Source: Stacks Project, Tag 0DJ8.
(blueprint: lem-pc-affine-tensor-cohomology-localization-isos). -/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory
open scoped TensorProduct

namespace RingTensorCohomology

/-- Localization compatibility of prescribed tensor-algebra cohomology lifts.
Source: Stacks Project, perfect.tex, Tag 0DJ8, affine displayed localization identities.
(blueprint: lem-pc-affine-tensor-cohomology-localization-isos)

Proof: Resolve M by the functorial A-K-flat resolution P. For source cohomology,
use derivedTensor_localization_cohomology on the balanced derived tensor model:
localize cohomology with its prescribed tensor-algebra action. Exact localization
and the tensor-localization formula identify this with the local derived tensor,
followed by scalar extension to D. These identifications are natural in M.
For the target, localization of P is K-flat over Aq and represents localized M.
Tensor associativity identifies its extension to D with the extension of P to D.
Exact localization commutes with cohomology and gives beta and the last isomorphism.
The scalar equations on the supplied lifts determine their tensor-algebra actions;
transport the canonical identifications along eS, eT, eSl and eTl. The equations
on f and hB identify the ring maps with the canonical localization maps. On the
local tensor algebra, f is itself a localization: first invert the elements of
A and B outside their contracted primes in A tensor_R B, and then invert the
remaining elements outside q'. The common R-localization does not change this
tensor algebra, since its denominators are already units in both local factors.
Thus extension along f is exact, justifying the last cohomology identification.
The local functorial resolution and the localization of P are two K-flat models
of localized M; quasi-isomorphism invariance identifies their cohomology naturally.
On the K-flat span both paths in the displayed square are the same localized augmentation
map; hence comparison compatibility in derivedTensor_localization_cohomology gives
its equality. The proof localizes source cohomology, never the R-K-flat complex as
an A tensor_R B complex. Empty prime spectra impose no localization obligations;
identity localizations and zero complexes satisfy the same natural identities. -/
theorem affineTensorCohomology_localization
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
          ∃ (alpha : S ⋙ ModuleCat.extendScalars (algebraMap (A ⊗[R] B) D) ≅
              extend A Aq ⋙ Sl ⋙ ModuleCat.extendScalars f)
            (beta : T ⋙ ModuleCat.extendScalars (algebraMap (A ⊗[R] B) D) ≅
              extend A Aq ⋙ Tl ⋙ ModuleCat.extendScalars f),
            Functor.whiskerRight c (ModuleCat.extendScalars (algebraMap (A ⊗[R] B) D)) ≫
                beta.hom = alpha.hom ≫
              Functor.whiskerLeft (extend A Aq)
                (Functor.whiskerRight cl (ModuleCat.extendScalars f)) ∧
            Nonempty (Tl ⋙ ModuleCat.extendScalars f ≅
              resolution Aq ⋙ extend Aq D ⋙
                HomologicalComplex.homologyFunctor (ModuleCat.{u} D) (.up ℤ) i) := by
  obtain ⟨alpha, beta, hAlpha, hBeta, hcomm⟩ :=
    affineTensorCohomology_localization_square R A B i S T eS eT c hS hT hc q'
      Rp Aq Bp D _hB f _hfA _hfB Sl Tl eSl eTl cl hSl hTl hcl
  have hf : f.Flat := affineTensorLocalization_flat R A B q' Rp Aq Bp D _hB f _hfA _hfB
  have htarget := affineTensorTarget_flat_extension Rp Aq Bp D i Tl eTl hTl f hf _hfA
  let alphaIso : S ⋙ ModuleCat.extendScalars (algebraMap (A ⊗[R] B) D) ≅
      extend A Aq ⋙ Sl ⋙ ModuleCat.extendScalars f :=
    NatIso.ofComponents alpha (fun g ↦ hAlpha _ _ g)
  let betaIso : T ⋙ ModuleCat.extendScalars (algebraMap (A ⊗[R] B) D) ≅
      extend A Aq ⋙ Tl ⋙ ModuleCat.extendScalars f :=
    NatIso.ofComponents beta (fun g ↦ hBeta _ _ g)
  refine ⟨alphaIso, betaIso, ?_, htarget⟩
  apply NatTrans.ext
  funext M
  exact hcomm M

end RingTensorCohomology
