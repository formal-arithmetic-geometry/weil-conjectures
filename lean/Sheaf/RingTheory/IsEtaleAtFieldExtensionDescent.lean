/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
module

public import Mathlib.RingTheory.Etale.Locus
public import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.FiniteStability
import Mathlib.RingTheory.Kaehler.TensorProduct
import Sheaf.AlgebraicGeometry.EtaleAtPrimeFlatUnramifiedCriterion
import WeilConjectures.RingTheory.FlatPermanence
import Sheaf.RingTheory.LocalRingHomTensorProductFieldExtensionFaithfullyFlat

/-!
# Descent of etaleness at a prime under field extension

Source: Stacks Project, Tags 0C4Y, 02L2, 02KY and 02VM, packaged in primewise affine form
(blueprint: lem-sc-etale-local-ring-faithfully-flat-descent).
-/

@[expose] public section

universe u v w z

open TensorProduct

namespace Algebra

/-- Etaleness at a prime descends under extension of the ground field.
Source: Stacks Project, Tags 0C4Y, 02L2, 02KY and 02VM
(blueprint: lem-sc-etale-local-ring-faithfully-flat-descent).

The algebra structure on `B ⊗[k] K` over `A ⊗[k] K` is induced by the tensor product of
`A → B` with the identity of `K`. The primes `p` and `p_K` in the node are the contractions
of `q` and `qK` along these algebra maps; they are auxiliary notation, not extra hypotheses.

Proof, following the four steps of the node:
1. The map `B_q → (B ⊗[k] K)_{qK}` is faithfully flat by
   [lem-sc-etale-local-ring-stalk-faithfully-flat].
2. Apply the same lemma to `A` to obtain faithful flatness over `A_p`. Finite presentation
   survives base change. The criterion [lem-sc-etale-at-prime-flat-unramified-criterion]
   makes the upper local ring flat over the upper base local ring. Compose flat maps and
   use [lem-weil-pbc-flat-permanence] to descend flatness to `A_p → B_q`.
3. By [lem-weil-pbc-kahler-differentials-base-change], the localized differentials upstairs
   are the faithfully flat scalar extension of those downstairs. They vanish upstairs by
   the same etale criterion, hence downstairs by [lem-sc-faithfully-flat-tensor-zero].
4. Apply [lem-sc-etale-at-prime-flat-unramified-criterion] to the finitely presented
   `A`-algebra `B`: flatness at `q` and vanishing differentials imply etaleness at `q`. -/
theorem IsEtaleAt.of_fieldExtension
    (k : Type u) (K : Type v) (A : Type w) (B : Type z)
    [Field k] [Field K] [Algebra k K] [CommRing A] [CommRing B]
    [Algebra k A] [Algebra A B] [Algebra k B] [IsScalarTower k A B]
    [FinitePresentation A B]
    (q : Ideal B) [q.IsPrime] (qK : Ideal (B ⊗[k] K)) [qK.IsPrime]
    (hq : Ideal.comap (Algebra.TensorProduct.includeLeftRingHom (R := k) (B := K)) qK = q) :
    letI : Algebra (A ⊗[k] K) (B ⊗[k] K) :=
      (Algebra.TensorProduct.map (IsScalarTower.toAlgHom k A B) (AlgHom.id k K)).toRingHom.toAlgebra
    IsEtaleAt (A ⊗[k] K) qK → IsEtaleAt A q := by
  let : Algebra (A ⊗[k] K) (B ⊗[k] K) :=
    (Algebra.TensorProduct.map (IsScalarTower.toAlgHom k A B)
      (AlgHom.id k K)).toRingHom.toAlgebra
  change IsEtaleAt (A ⊗[k] K) qK → IsEtaleAt A q
  intro he
  let : IsEtaleAt (A ⊗[k] K) qK := he
  have ht : IsScalarTower A (A ⊗[k] K) (B ⊗[k] K) := by
    apply IsScalarTower.of_algebraMap_eq'
    ext a
    simp [RingHom.algebraMap_toAlgebra, Algebra.TensorProduct.map_tmul]
  let := ht
  have hpush : Algebra.IsPushout A B (A ⊗[k] K) (B ⊗[k] K) := by
    apply Algebra.IsPushout.tensorProduct_tensorProduct k K A B
    ext x
    simp [RingHom.algebraMap_toAlgebra, Algebra.TensorProduct.map_tmul]
  let := hpush
  let : Algebra.IsPushout A (A ⊗[k] K) B (B ⊗[k] K) := hpush.symm
  have hfp : FinitePresentation (A ⊗[k] K) (B ⊗[k] K) := by
    exact FinitePresentation.equiv (Algebra.IsPushout.equiv A (A ⊗[k] K) B
      (B ⊗[k] K))
  let := hfp
  let C := Localization.AtPrime qK
  let D := Localization.AtPrime q
  let f : D →+* C := Localization.localRingHom q qK
    Algebra.TensorProduct.includeLeftRingHom hq.symm
  let : Algebra D C := f.toAlgebra
  have htBC : IsScalarTower B D C := .of_algebraMap_eq fun b ↦
    (Localization.localRingHom_to_map q qK
      Algebra.TensorProduct.includeLeftRingHom hq.symm b).symm
  let := htBC
  have htAC : IsScalarTower A D C := IsScalarTower.to₁₃₄ A B D C
  let := htAC
  have hff : Module.FaithfullyFlat D C :=
    Localization.localRingHom_tensorProduct_fieldExtension_faithfullyFlat
      (A := A) q qK hq.symm
  let := hff
  -- Work over A first, avoiding the auxiliary map between the base local rings.
  have hflatC : Module.Flat A C := by
    let pK := qK.under (A ⊗[k] K)
    have hf := (isEtaleAt_iff_exists_away_etale_iff_flat_localized_kaehler qK).2.mp he
    let := (Localization.localRingHom pK qK
      (algebraMap (A ⊗[k] K) (B ⊗[k] K)) rfl).toAlgebra
    have : IsScalarTower (A ⊗[k] K) (Localization.AtPrime pK) C :=
      .of_algebraMap_eq fun a ↦ (Localization.localRingHom_to_map pK qK
        (algebraMap (A ⊗[k] K) (B ⊗[k] K)) rfl a).symm
    have : Module.Flat (Localization.AtPrime pK) C := hf.1
    have : Module.Flat (A ⊗[k] K) C :=
      (Module.flat_iff_of_isLocalization (Localization.AtPrime pK) pK.primeCompl C).mp
        inferInstance
    exact Module.Flat.trans A (A ⊗[k] K) C
  have hflatD : Module.Flat A D := by
    have hf := RingHom.flat_of_flat_module_of_faithfullyFlat_module
      (M := C) (algebraMap A D) (by
        have hm : Module.compHom C (algebraMap A D) = (inferInstance : Module A C) := by
          apply Module.ext
          funext a c
          exact IsScalarTower.algebraMap_smul D a c
        change @Module.Flat A C _ _ (Module.compHom C (algebraMap A D))
        rw [hm]
        exact hflatC)
    exact (RingHom.flat_algebraMap_iff).mp hf
  -- Localize differentials, apply base change, and cancel the intervening tensor products.
  have hΩ : Subsingleton (LocalizedModule q.primeCompl (KaehlerDifferential A B)) := by
    let e₁ := TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl C C)
      (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale A B D).symm
    let e₂ := TensorProduct.AlgebraTensorModule.cancelBaseChange B D C C
      (KaehlerDifferential A B)
    let e₃ := (TensorProduct.AlgebraTensorModule.cancelBaseChange B (B ⊗[k] K) C C
      (KaehlerDifferential A B)).symm
    let e₄ := TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl C C)
      (KaehlerDifferential.tensorKaehlerEquiv A (A ⊗[k] K) B (B ⊗[k] K))
    let e₅ := KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale
      (A ⊗[k] K) (B ⊗[k] K) C
    have : Subsingleton (C ⊗[D] KaehlerDifferential A D) :=
      (e₁.trans (e₂.trans (e₃.trans (e₄.trans e₅)))).subsingleton
    have : Subsingleton (KaehlerDifferential A D) :=
      Module.FaithfullyFlat.lTensor_reflects_triviality D C _
    exact (IsLocalizedModule.iso q.primeCompl (KaehlerDifferential.map A A B D)).subsingleton
  apply (isEtaleAt_iff_exists_away_etale_iff_flat_localized_kaehler q).2.mpr
  refine ⟨?_, hΩ⟩
  let := (Localization.localRingHom (q.under A) q (algebraMap A B) rfl).toAlgebra
  have : IsScalarTower A (Localization.AtPrime (q.under A)) D :=
    .of_algebraMap_eq fun a ↦
      (Localization.localRingHom_to_map (q.under A) q (algebraMap A B) rfl a).symm
  exact (Module.flat_iff_of_isLocalization (Localization.AtPrime (q.under A))
    (q.under A).primeCompl D).mpr hflatD

end Algebra
