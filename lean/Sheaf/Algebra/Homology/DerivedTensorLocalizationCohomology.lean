/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
-/
import Sheaf.Algebra.Homology.BaseDerivedTensorCohomologyModel
import Sheaf.Algebra.Homology.RingTensorCohomology
import Mathlib.RingTheory.Localization.AtPrime.Basic

/-! # Localization of cohomology of a derived tensor

Source: Stacks Project, perfect.tex, Tag 0DJ8, the affine proof of
lemma-single-complex-base-change-condition
(blueprint: lem-pc-derived-tensor-localization-cohomology).

The existing cohomology models specify the derived universal property, coefficient
algebra action and comparison maps. The theorem is independent of the choices of models.
`P` is a functorial A-K-flat resolution; `J` is localization of A-complexes. The ordinary
complex on the comparison's target therefore computes the A-derived tensor, both before
and after localization. Naturality is expressed using maps between cohomology models:
their equations identify them with the maps induced by a complex morphism and the unique
counit-compatible comparison between the two derived functors.
-/

set_option autoImplicit false

universe u w

open CategoryTheory
open scoped TensorProduct ChangeOfRings

attribute [local instance] Algebra.TensorProduct.rightAlgebra

namespace RingTensorCohomology

variable (R A B Rp Aq Bp D : Type u)
  [CommRing R] [CommRing A] [CommRing B] [CommRing Rp] [CommRing Aq]
  [CommRing Bp] [CommRing D]
  [Algebra R A] [Algebra R B] [Algebra R Rp] [Algebra A Aq] [Algebra B Bp]
  [Algebra R Aq] [Algebra R Bp] [Algebra Rp Aq] [Algebra Rp Bp]
  [tRA : IsScalarTower R A Aq] [tRpA : IsScalarTower R Rp Aq]
  [tRB : IsScalarTower R B Bp] [tRpB : IsScalarTower R Rp Bp]
  [Algebra (A ⊗[R] B) D] [Algebra (Aq ⊗[Rp] Bp) D]
  [Algebra A D] [Algebra B D] [Algebra Aq D] [Algebra Bp D]
  [tAD : IsScalarTower A (A ⊗[R] B) D]
  [tBD : IsScalarTower B (A ⊗[R] B) D]
  [tAqD : IsScalarTower Aq (Aq ⊗[Rp] Bp) D]
  [tBpD : IsScalarTower Bp (Aq ⊗[Rp] Bp) D]
  [tAAqD : IsScalarTower A Aq D] [tBBpD : IsScalarTower B Bp D]
  [HasDerivedCategory.{w} (ModuleCat.{u} R)]
  [HasDerivedCategory.{w} (ModuleCat.{u} B)]
  [HasDerivedCategory.{w} (ModuleCat.{u} Rp)]
  [HasDerivedCategory.{w} (ModuleCat.{u} Bp)]

set_option quotPrecheck false in
local notation "P" => resolution A
set_option quotPrecheck false in
local notation "J" => extend A Aq
set_option quotPrecheck false in
local notation "ML" => fun M => ModuleCat.BaseDerivedTensorCohomologyModel R A B ((P).obj M) D
set_option quotPrecheck false in
local notation "MR" => fun M => ModuleCat.BaseDerivedTensorCohomologyModel Rp Aq Bp
  ((J).obj ((P).obj M)) D
set_option quotPrecheck false in
local notation "EL" => ModuleCat.extendScalars (algebraMap (A ⊗[R] B) D)
set_option quotPrecheck false in
local notation "ER" => ModuleCat.extendScalars (algebraMap (Aq ⊗[Rp] Bp) D)

include tRA tRpA tRB tRpB tAD tBD tAqD tBpD tAAqD tBBpD in
/-- Localization of derived tensor cohomology, with naturality and comparison compatibility.
Source: Stacks Project, perfect.tex, Tag 0DJ8, affine displayed localization identity
(blueprint: lem-pc-derived-tensor-localization-cohomology).

Proof, following all three steps of the node:
1. Resolve M by P over A and resolve B over R. The balanced model of
   `lem-pc-balanced-derived-tensor-model` computes the R-derived tensor. Localization
   preserves K-flatness (`lem-pc-kflat-pullback-preservation`, one-point ringed spaces)
   and quasi-isomorphisms (`lem-weil-pbc-localization-module-exact`). Tensor associativity
   and `lem-weil-pbc-localization-tensor-product` identify the localized total complex
   with the total tensor over Rp of the localized factors.
2. Exact localization commutes with cohomology. The identifications preserve the
   A-action on P and the B-action via multiplication endomorphisms in D(R), by
   `lem-pc-derived-tensor-action-naturality`. Localizing the roofs representing these
   endomorphisms preserves their action. The same termwise identification applied to
   the resolution augmentation gives compatibility with the comparison map. Chain
   maps between resolutions give naturality in M. Counit-compatible transformations
   identify arbitrary derived models, so the naturality equation applies to all models.
3. Apply `lem-pc-derived-tensor-flat-second-localization` to the flat localization
   from B localized at p to Bp. Transitivity of localization identifies subsequent
   scalar extension to D with localization of the original A-tensor-B cohomology at
   q'. Both this step and step 2 preserve the comparison map and naturality. On the
   target, the tensor-associativity map sends d tensor x to d tensor (1 tensor x);
   since P and its localization are K-flat over A and Aq, these ordinary complexes
   compute precisely the two A-derived comparison targets. -/
theorem derivedTensor_localization_cohomology
    (q' : Ideal (A ⊗[R] B)) [q'.IsPrime]
    (q : Ideal A) [q.IsPrime] (p' : Ideal B) [p'.IsPrime]
    (p : Ideal R) [p.IsPrime]
    (hq : q = q'.comap (algebraMap A (A ⊗[R] B)))
    (hp' : p' = q'.comap Algebra.TensorProduct.includeRight.toRingHom)
    (hp : p = q.comap (algebraMap R A))
    [IsLocalization.AtPrime Rp p] [IsLocalization.AtPrime Aq q]
    [IsLocalization.AtPrime Bp p'] [IsLocalization.AtPrime D q'] :
    ∀ i : ℤ, ∃ e : ∀ (M : CochainComplex (ModuleCat.{u} A) ℤ)
        (L : (ML) M) (K : (MR) M),
        (EL).obj (L.cohomology i) ≅ (ER).obj (K.cohomology i),
      (∀ (M : CochainComplex (ModuleCat.{u} A) ℤ) (L : (ML) M) (K : (MR) M)
          (τ :
            ((ModuleCat.extendScalars ((algebraMap (A ⊗[R] B) D).comp
              (algebraMap A (A ⊗[R] B)))).mapHomologicalComplex (.up ℤ)).obj ((P).obj M) ≅
            ((ModuleCat.extendScalars ((algebraMap (Aq ⊗[Rp] Bp) D).comp
              (algebraMap Aq (Aq ⊗[Rp] Bp)))).mapHomologicalComplex (.up ℤ)).obj
                ((J).obj ((P).obj M))),
          (∀ (j : ℤ) (d : D) (x : ((P).obj M).X j),
            τ.hom.f j (d ⊗ₜ[A, (algebraMap (A ⊗[R] B) D).comp
              (algebraMap A (A ⊗[R] B))] x) =
              d ⊗ₜ[Aq, (algebraMap (Aq ⊗[Rp] Bp) D).comp
                (algebraMap Aq (Aq ⊗[Rp] Bp))] ((1 : Aq) ⊗ₜ[A, algebraMap A Aq] x)) →
          L.localizedComparison i ≫ HomologicalComplex.homologyMap τ.hom i =
            (e M L K).hom ≫ K.localizedComparison i) ∧
      (∀ (M N : CochainComplex (ModuleCat.{u} A) ℤ) (f : M ⟶ N)
          (L : (ML) M) (K : (MR) M) (L' : (ML) N) (K' : (MR) N)
          (δ : L.derived ⟶ L'.derived) (ε : K.derived ⟶ K'.derived)
          (g : L.cohomology i ⟶ L'.cohomology i)
          (h : K.cohomology i ⟶ K'.cohomology i),
        Functor.whiskerLeft (DerivedCategory.Qh (C := ModuleCat.{u} R)) δ ≫ L'.counit = L.counit →
        Functor.whiskerLeft (DerivedCategory.Qh (C := ModuleCat.{u} Rp)) ε ≫ K'.counit = K.counit →
        (ModuleCat.restrictScalars.{u}
          (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom).map g ≫
                (L'.cohomologyIso i).hom =
          (L.cohomologyIso i).hom ≫ (DerivedCategory.homologyFunctor (ModuleCat.{u} B) i).map
            (L.derived.map (DerivedCategory.Qh.map ((HomotopyCategory.quotient (ModuleCat.{u} R)
                (.up ℤ)).map
              ((restrict R A).map ((P).map f))))) ≫
            (DerivedCategory.homologyFunctor (ModuleCat.{u} B) i).map (δ.app
                (DerivedCategory.Qh.obj ((HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ)).obj
              ((restrict R A).obj ((P).obj N))))) →
        (ModuleCat.restrictScalars.{u}
          (Algebra.TensorProduct.includeRight : Bp →ₐ[Rp] Aq ⊗[Rp] Bp).toRingHom).map h ≫
                (K'.cohomologyIso i).hom =
          (K.cohomologyIso i).hom ≫ (DerivedCategory.homologyFunctor (ModuleCat.{u} Bp) i).map
            (K.derived.map (DerivedCategory.Qh.map ((HomotopyCategory.quotient (ModuleCat.{u} Rp)
                (.up ℤ)).map
              ((restrict Rp Aq).map ((J).map ((P).map f)))))) ≫
            (DerivedCategory.homologyFunctor (ModuleCat.{u} Bp) i).map (ε.app
                (DerivedCategory.Qh.obj ((HomotopyCategory.quotient (ModuleCat.{u} Rp) (.up ℤ)).obj
              ((restrict Rp Aq).obj ((J).obj ((P).obj N)))))) →
        (EL).map g ≫ (e N L' K').hom = (e M L K).hom ≫ (ER).map h) := by
  sorry

end RingTensorCohomology
