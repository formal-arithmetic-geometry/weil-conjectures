/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.FiniteFreeCoefficients.Sites.FiniteFreeCoefficientExtensionData
import WeilConjectures.AlgebraicGeometry.Etale.Scalar.EtaleScalarFlatModel
import all WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientDirectImage
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison

/-! # Finite-ring scalar and direct-image foundations

Source: blueprint latest, sec-smooth-purity/sk-lem-sp-tower,
lem-coef-finite-free-extension.proof.md.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option Elab.async false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.FiniteCoefficientAdjoints
open scoped CategoryTheory.Functor
namespace WeilConjectures.FiniteFreeCoefficients

attribute [local irreducible] CategoryTheory.Functor.leftDerivedFunctor
  CategoryTheory.Functor.rightDerivedFunctor CategoryTheory.Functor.mapDerivedCategory
  AlgebraicGeometry.ProEtale.pbcFixedScalarExtension
  AlgebraicGeometry.ProEtale.pbcFixedScalarExtensionComp
  AlgebraicGeometry.ProEtale.pbcComparisonReduction
  _root_.DerivedCategory.monoidalClosed
  _root_.DerivedCategory.instMonoidalCategory_weilConjectures
  _root_.DerivedCategory.commShift₂CurriedTensor

private theorem etale_scalar_ctf
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (X : Scheme.{u}) [IsNoetherian X]
    (K : Cat A X) (hK : Ctf A X K) :
    Ctf B X ((Etale.scalarExtension φ X).obj K) := by
  obtain ⟨a, b, hab, ht⟩ := hK.2
  have hb : _root_.DerivedCategory.TStructure.t.bounded K := by
    obtain ⟨c, d, _, hz⟩ := hK.1.2
    exact ⟨⟨c, (_root_.DerivedCategory.isGE_iff _ c).2 fun q hq ↦ hz q (.inl hq)⟩,
      ⟨d, (_root_.DerivedCategory.isLE_iff _ d).2 fun q hq ↦ hz q (.inr hq)⟩⟩
  let Kb : _root_.DerivedCategory.Bounded
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) := ⟨K, hb⟩
  have hs := Etale.exists_etaleScalarFlatModel X A B φ a b hab Kb hK.1.1 ht
  have ht' := hs.2.2.2.2
  have hh := _root_.DerivedCategory.homologyConcentratedIn_of_torAmplitudeIn
    (Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.1 ht')
  refine ⟨⟨hs.2.2.2.1, a, b, hab, ?_⟩, a, b, hab, ht'⟩
  intro q hq
  exact hq.elim
    (fun h ↦ (_root_.DerivedCategory.isGE_iff _ a).1 hh.1 q h)
    (fun h ↦ (_root_.DerivedCategory.isLE_iff _ b).1 hh.2 q h)

private theorem boundedConstructible_iff_source
    (A : Type (u + 1)) [CommRing A] [Finite A] (X : Scheme.{u}) (K : Cat A X) :
    Etale.DerivedCategory.isBoundedConstructible A X K ↔
      Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} A) X K := by
  constructor
  · rintro ⟨hc, a, b, hab, hz⟩
    refine ⟨⟨⟨a, ?_⟩, ⟨b, ?_⟩⟩, fun q ↦ ?_⟩
    · exact (_root_.DerivedCategory.isGE_iff K a).2 fun q hq ↦ hz q (.inl hq)
    · exact (_root_.DerivedCategory.isLE_iff K b).2 fun q hq ↦ hz q (.inr hq)
    · exact (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).1 (hc q)
  · rintro ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, hc⟩
    refine ⟨fun q ↦ (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).2 (hc q),
      min a b, b, min_le_right _ _, fun q hq ↦ ?_⟩
    rcases hq with hq | hq
    · exact (_root_.DerivedCategory.isGE_iff K a).1 ha q (hq.trans_le (min_le_left _ _))
    · exact (_root_.DerivedCategory.isLE_iff K b).1 hb q hq

private theorem ctf_iff_source
    (A : Type (u + 1)) [CommRing A] [Finite A] (X : Scheme.{u}) (K : Cat A X) :
    Ctf A X K ↔
      Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) X K := by
  constructor
  · rintro ⟨hc, a, b, _, ht⟩
    exact ⟨(boundedConstructible_iff_source A X K).1 hc, a, b,
      Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.1 ht⟩
  · rintro ⟨hc, a, b, ht⟩
    exact ⟨(boundedConstructible_iff_source A X K).2 hc, min a b, b, min_le_right _ _,
      Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.2
        (ht.mono (min_le_left _ _) le_rfl)⟩

private theorem pro_scalar_ctf
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (X : Scheme.{u}) [IsNoetherian X]
    (K : Sites.D true A X) (hK : Sites.Ctf true A X K) :
    Sites.Ctf true B X ((Sites.scalar true φ X).obj K) := by
  obtain ⟨⟨K', hK', ⟨e⟩⟩, a, b, ht⟩ := hK
  have ht' := (ProEtale.DerivedCategory.torAmplitudeIn_mapDerivedCategory_iff a b K').1
    ((ProEtale.DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} A) X a b).prop_of_iso
      e.symm ht)
  have hsrc : Ctf A X K' := (ctf_iff_source A X K').2 ⟨hK', a, b, ht'⟩
  have hsc := (ctf_iff_source B X _).1 (etale_scalar_ctf φ X K' hsrc)
  have hν := ProEtale.DerivedCategory.constructibleFiniteTor_mapDerivedCategory B hsc
  let eS : (Sites.scalar true φ X).obj K ≅
      (Sites.nu B X).obj ((Etale.scalarExtension φ X).obj K') :=
    (Sites.scalar true φ X).mapIso e.symm ≪≫ (Sites.scalarSite φ X).app K'
  exact (ProEtale.DerivedCategory.constructibleFiniteTor
    (ModuleCat.{u + 1} B) X).prop_of_iso eS.symm hν

private theorem stage_scalar_ctf
    (pro : Bool) (D : FiniteFieldDatum.{u}) {A B : Type (u + 1)}
    [CommRing A] [CommRing B] [Finite A] [Finite B] (φ : A →+* B) (X : Scheme.{u})
    [X.Over (Spec (.of D.k))] [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))] (K : Sites.D pro A X) (hK : Sites.Ctf pro A X K) :
    Sites.Ctf pro B X ((Sites.scalar pro φ X).obj K) := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of D.k))
  have : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of D.k))
  have : IsNoetherian X := {}
  cases pro
  · exact etale_scalar_ctf φ X K hK
  · exact pro_scalar_ctf φ X K hK

private theorem etale_stage_scalar_ctf
    (D : FiniteFieldDatum.{u}) {A B : Type (u + 1)} [CommRing A] [CommRing B]
    [Finite A] [Finite B] (φ : A →+* B) (X : Scheme.{u})
    [X.Over (Spec (.of D.k))] [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))] (K : Cat A X) (hK : Ctf A X K) :
    Ctf B X ((Etale.scalarExtension φ X).obj K) := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of D.k))
  have : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of D.k))
  have : IsNoetherian X := {}
  exact etale_scalar_ctf φ X K hK

private theorem etale_stage_direct_iso
    (D : FiniteFieldDatum.{u}) {A B : Type (u + 1)} [CommRing A] [CommRing B]
    [Finite A] [Finite B] (φ : A →+* B) {T X : Scheme.{u}}
    [T.Over (Spec (.of D.k))] [X.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (T ↘ Spec (.of D.k))] [QuasiCompact (T ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    (f : T ⟶ X) [f.IsOver (Spec (.of D.k))]
    [LocallyOfFiniteType f] [QuasiCompact f]
    (K : Cat A T) (hK : Ctf A T K) :
    IsIso (Etale.finiteCoefficientDirectImageMap φ f K) := by
  let := φ.toAlgebra
  have : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
  obtain ⟨c, d, _, hz⟩ := hK.1.2
  have : K.IsGE c := (_root_.DerivedCategory.isGE_iff K c).2
    (fun q hq ↦ hz q (.inl hq))
  have hs := etale_stage_scalar_ctf D φ T K hK
  obtain ⟨a, b, _, hzs⟩ := hs.1.2
  have : ((Etale.scalarExtension φ T).obj K).IsGE a :=
    (_root_.DerivedCategory.isGE_iff _ a).2 (fun q hq ↦ hzs q (.inl hq))
  exact Etale.coefficientMap_isIso_of_geometry (A := A) (B := B)
    (T ↘ Spec (.of D.k)) (X ↘ Spec (.of D.k)) f (comp_over f (Spec (.of D.k)))
    K a c d (fun q hq ↦ hz q (.inr hq))

private theorem pro_stage_direct_iso
    (D : FiniteFieldDatum.{u}) {A B : Type (u + 1)} [CommRing A] [CommRing B]
    [Finite A] [Finite B] (φ : A →+* B) {T X : Scheme.{u}}
    [T.Over (Spec (.of D.k))] [X.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (T ↘ Spec (.of D.k))] [QuasiCompact (T ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    (f : T ⟶ X) [f.IsOver (Spec (.of D.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (K : Sites.D true A T) (hK : Sites.Ctf true A T K) :
    IsIso (Sites.direct true φ f K) := by
  obtain ⟨⟨K', hbc, ⟨e⟩⟩, a, b, ht⟩ := hK
  have ht' := (ProEtale.DerivedCategory.torAmplitudeIn_mapDerivedCategory_iff a b K').1
    ((ProEtale.DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} A) T a b).prop_of_iso
      e.symm ht)
  have hK' := (ctf_iff_source A T K').2 ⟨hbc, a, b, ht'⟩
  have hS := etale_stage_scalar_ctf D φ T K' hK'
  obtain ⟨r, q, _, hz⟩ := hK'.1.2
  obtain ⟨r', q', _, hz'⟩ := hS.1.2
  have := etale_stage_direct_iso D φ f K' hK'
  have hs := ProEtale.finiteCoefficientDirectImageMap_etaleOrigin_isIso_of_isIso φ f K'
    ⟨r, (_root_.DerivedCategory.isGE_iff K' r).2 (fun k hk ↦ hz k (.inl hk))⟩
    ⟨r', (_root_.DerivedCategory.isGE_iff _ r').2 (fun k hk ↦ hz' k (.inl hk))⟩
  have hcomposite : IsIso (Sites.direct true φ f ((Sites.nu A T).obj K') ≫
      (Sites.push true B f).map ((Sites.scalarSite φ T).hom.app K')) := by
    simpa only [Sites.direct, Sites.nu, Sites.push, Sites.scalarSite, Sites.scalar, id_eq] using hs
  have htail : IsIso
      ((Sites.push true B f).map ((Sites.scalarSite φ T).hom.app K')) :=
    ((Sites.push true B f).mapIso ((Sites.scalarSite φ T).app K')).isIso_hom
  have hdir : IsIso (Sites.direct true φ f ((Sites.nu A T).obj K')) :=
    @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ htail hcomposite
  let α : Sites.push true A f ⋙ Sites.scalar true φ X ⟶
      Sites.scalar true φ T ⋙ Sites.push true B f := {
    app := Sites.direct true φ f
    naturality := fun _ _ g ↦ by
      simpa only [Sites.scalar, Sites.push, Sites.direct, id_eq, Functor.comp_map,
        Functor.comp_obj] using
        ProEtale.finiteCoefficientDirectImageMap_naturality φ f g }
  have hα : IsIso (α.app ((Sites.nu A T).obj K')) := hdir
  have he := (NatTrans.isIso_app_iff_of_iso α e).1 hα
  simpa only [α] using he

/-- Scalar preservation and direct-image invertibility for arbitrary finite coefficient rings.

Source: blueprint latest, lem-coef-finite-free-extension.proof.md, paragraphs 1--2;
the generic finite-ring proof of lem-coef-finite-direct-image and the flat-model theorem.
(blueprint: lem-sf-normalized-stage-finite-ring-foundations).

Proof: a finite-type quasi-compact scheme over the finite-field datum is Noetherian.
A bounded constructible flat model in the given Tor interval remains constructible
and in that interval after coefficient extension; testing the regular module gives
bounded cohomology. For a pro-etale input, choose its etale origin, reflect the Tor
interval, apply the etale result and transport by the scalar/site comparison.
The generic coefficient direct-image theorem applies to the bounded input and the
bounded scalar extension on the etale site. Its etale-origin square makes the
pro-etale direct map invertible at origins after cancellation of the scalar/site
isomorphism. Naturality and the origin isomorphism give the assertion at every ctf
input. No uniformizer presentation or flatness of the coefficient homomorphism is
used. -/
theorem finite_ring_scalar_direct_foundations
    (D : FiniteFieldDatum.{u}) {A B : Type (u + 1)} [CommRing A] [CommRing B]
    [Finite A] [Finite B] (φ : A →+* B) (T X : Scheme.{u})
    [T.Over (Spec (.of D.k))] [X.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (T ↘ Spec (.of D.k))] [QuasiCompact (T ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    (f : T ⟶ X) [f.IsOver (Spec (.of D.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] :
    (∀ (pro : Bool) (K : Sites.D pro A T), Sites.Ctf pro A T K →
      Sites.Ctf pro B T ((Sites.scalar pro φ T).obj K)) ∧
    (∀ (pro : Bool) (K : Sites.D pro A X), Sites.Ctf pro A X K →
      Sites.Ctf pro B X ((Sites.scalar pro φ X).obj K)) ∧
    (∀ (pro : Bool) (K : Sites.D pro A T), Sites.Ctf pro A T K →
      IsIso (Sites.direct pro φ f K)) := by
  refine ⟨fun pro K hK ↦ stage_scalar_ctf pro D φ T K hK,
    fun pro K hK ↦ stage_scalar_ctf pro D φ X K hK, ?_⟩
  intro pro K hK
  cases pro
  · exact etale_stage_direct_iso D φ f K hK
  · exact pro_stage_direct_iso D φ f K hK

end WeilConjectures.FiniteFreeCoefficients
