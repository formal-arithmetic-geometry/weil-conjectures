/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Etale.Descent
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.Localization.BaseChange
public import WeilConjectures.RingTheory.Etale.IntegralClosureSpreading

/-!
# Descending étaleness at a prime along a flat base change

Let `B → B₁` be flat, `P₁` a prime of `B₁` lying over the prime `P` of `B`, and `T` a finitely
presented `B`-algebra. If `T` becomes étale over the local ring `(B₁)_{P₁}` after base change,
then `T` is étale over `B` near `P`: there is `g ∉ P` with `B_g ⊗[B] T` étale over `B_g`
(`Algebra.exists_etale_localizationAway_of_formallyEtale_atPrime`).

The proof descends étaleness along the faithfully flat local homomorphism `B_P → (B₁)_{P₁}`
(`Algebra.Etale.of_etale_tensorProduct_of_faithfullyFlat`) and spreads it out from `B_P` using
openness of the étale locus (`Algebra.exists_etale_localizationAway_of_isLocalization`).

This is the descent step of the trait case of the spreading theorem (blueprint
`sbc-thm-spreading-finite-etale-galois`).
-/

@[expose] public section

open TensorProduct

namespace Algebra

/-- If a finitely presented `B`-algebra `T` is étale over the localization `B_P` at a prime `P`,
it is étale over `B_g` for some `g ∉ P`. -/
theorem exists_etale_localizationAway_of_etale_atPrime {B T : Type*} [CommRing B] [CommRing T]
    [Algebra B T] [Algebra.FinitePresentation B T] (P : Ideal B) [P.IsPrime]
    [Algebra.FormallyEtale (Localization.AtPrime P) (Localization.AtPrime P ⊗[B] T)] :
    ∃ g ∉ P, Algebra.Etale (Localization.Away g) (Localization.Away g ⊗[B] T) := by
  let R := Localization.AtPrime P
  let : Algebra T (R ⊗[B] T) := Algebra.TensorProduct.rightAlgebra
  have : IsLocalization (Algebra.algebraMapSubmonoid T P.primeCompl) (R ⊗[B] T) :=
    IsLocalization.tensorRight _ P.primeCompl
  have : FormallyEtale B R := .of_isLocalization P.primeCompl
  have : FormallyEtale B (R ⊗[B] T) := .comp B R _
  obtain ⟨_, ⟨g, hg, rfl⟩, hm⟩ :=
    exists_etale_localizationAway_of_isLocalization (B := B) (L := R ⊗[B] T)
      (Algebra.algebraMapSubmonoid T P.primeCompl)
  refine ⟨g, hg, ?_⟩
  let Bg := Localization.Away g
  let : Algebra T (Bg ⊗[B] T) := Algebra.TensorProduct.rightAlgebra
  have : IsLocalization (Algebra.algebraMapSubmonoid T (.powers g)) (Bg ⊗[B] T) :=
    IsLocalization.tensorRight _ (.powers g)
  have : IsLocalization.Away (algebraMap B T g) (Bg ⊗[B] T) := by
    rwa [Algebra.algebraMapSubmonoid, Submonoid.map_powers] at this
  let e := (IsLocalization.algEquiv (.powers (algebraMap B T g))
    (Localization.Away (algebraMap B T g)) (Bg ⊗[B] T)).restrictScalars B
  have : FormallyEtale B (Bg ⊗[B] T) := .of_equiv e
  have : FormallyUnramified B Bg := .of_isLocalization (.powers g)
  exact ⟨.of_restrictScalars (R := B), inferInstance⟩

/-- **Descending étaleness at a prime along a flat base change.** Let `B → B₁` be flat, `P₁` a
prime of `B₁` and `T` a finitely presented `B`-algebra such that `(B₁)_{P₁} ⊗[B] T` is
(formally) étale over `(B₁)_{P₁}`. Then there is `g ∈ B` not in `P = P₁ ∩ B` such that
`B_g ⊗[B] T` is étale over `B_g`.

This is the descent step of the trait case of the spreading theorem (blueprint
`sbc-thm-spreading-finite-etale-galois`). -/
theorem exists_etale_localizationAway_of_formallyEtale_atPrime {B B₁ T : Type*} [CommRing B]
    [CommRing B₁] [CommRing T] [Algebra B B₁] [Module.Flat B B₁] [Algebra B T]
    [Algebra.FinitePresentation B T] (P₁ : Ideal B₁) [P₁.IsPrime]
    [Algebra.FormallyEtale (Localization.AtPrime P₁) (Localization.AtPrime P₁ ⊗[B] T)] :
    ∃ g ∉ P₁.under B, Algebra.Etale (Localization.Away g) (Localization.Away g ⊗[B] T) := by
  let P := P₁.under B
  let R := Localization.AtPrime P
  let R₁ := Localization.AtPrime P₁
  let : Algebra R R₁ := Localization.AtPrime.algebraOfLiesOver P P₁
  have : IsLocalHom (algebraMap R R₁) :=
    Localization.isLocalHom_localRingHom P P₁ (algebraMap B B₁) Ideal.LiesOver.over
  have : Module.FaithfullyFlat R R₁ := .of_flat_of_isLocalHom
  have : Algebra.Etale R₁ (R₁ ⊗[B] T) := ⟨inferInstance, inferInstance⟩
  have : Algebra.Etale R₁ (R₁ ⊗[R] (R ⊗[B] T)) :=
    .of_equiv (Algebra.TensorProduct.cancelBaseChange B R R₁ R₁ T).symm
  have : Algebra.Etale R (R ⊗[B] T) := .of_etale_tensorProduct_of_faithfullyFlat R₁
  exact exists_etale_localizationAway_of_etale_atPrime P

/-- **Descending étaleness at a prime along a flat base change**, with the hypothesis on a basic
open neighbourhood of `P₁`. Let `B → B₁` be flat, `P₁` a prime of `B₁`, `T` a finitely presented
`B`-algebra and `h ∉ P₁` such that `(B₁)_h ⊗[B] T` (i.e. `(B₁ ⊗[B] T)_h`) is étale over
`(B₁)_h`. Then there is `g ∈ B` not in `P = P₁ ∩ B` such that `B_g ⊗[B] T` is étale over `B_g`.

This is the descent step of the trait case of the spreading theorem (blueprint
`sbc-thm-spreading-finite-etale-galois`). -/
theorem exists_etale_localizationAway_of_etale_localizationAway {B B₁ T : Type*} [CommRing B]
    [CommRing B₁] [CommRing T] [Algebra B B₁] [Module.Flat B B₁] [Algebra B T]
    [Algebra.FinitePresentation B T] (P₁ : Ideal B₁) [P₁.IsPrime] {h : B₁} (hh : h ∉ P₁)
    [Algebra.Etale (Localization.Away h) (Localization.Away h ⊗[B] T)] :
    ∃ g ∉ P₁.under B, Algebra.Etale (Localization.Away g) (Localization.Away g ⊗[B] T) := by
  let B₁h := Localization.Away h
  let P₁' := P₁.map (algebraMap B₁ B₁h)
  have hdisj : Disjoint (Submonoid.powers h : Set B₁) P₁ :=
    (Ideal.disjoint_powers_iff_notMem _ (Ideal.IsPrime.isRadical ‹_›)).mpr hh
  have : P₁'.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint (.powers h) B₁h P₁ ‹_› hdisj
  have hcomap : P₁'.under B₁ = P₁ :=
    IsLocalization.under_map_of_isPrime_disjoint (.powers h) B₁h ‹_› hdisj
  have : Module.Flat B B₁h := .trans B B₁ B₁h
  let R₁' := Localization.AtPrime P₁'
  have : FormallyEtale R₁' (R₁' ⊗[B] T) :=
    .of_equiv (Algebra.TensorProduct.cancelBaseChange B B₁h R₁' R₁' T)
  obtain ⟨g, hg, H⟩ :=
    exists_etale_localizationAway_of_formallyEtale_atPrime (B := B) (B₁ := B₁h) (T := T) P₁'
  refine ⟨g, ?_, H⟩
  rwa [← hcomap, Ideal.under_under]

end Algebra
