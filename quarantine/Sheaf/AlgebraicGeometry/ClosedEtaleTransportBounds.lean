/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q22
-/
module

public import Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients
public import Sheaf.Paper.ConstructibleExceptionalInverseImage
public import Sheaf.AlgebraicGeometry.OpenComplementCondition
public import Sheaf.AlgebraicGeometry.IntrinsicConstructibleIntervals
public import Sheaf.Paper.FiniteTorAmplitudeSites
public import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
public import Sheaf.AlgebraicGeometry.EtaleClosedAmbientAdjoint
import Sheaf.Paper.FiniteRingConstructibleDerivedOrigin
import Sheaf.AlgebraicGeometry.EtaleClosedOutputBounds
import Sheaf.AlgebraicGeometry.ComparisonTorInterval
import Sheaf.Paper.ProEtaleConstantModuleConstructibility
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekToLowerStar
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Closed-support bounds transported from the etale site

Source: main-20261015, thm-pur-general-admissibility.proof.md, Step 2
(blueprint: lem-pur-closed-etale-transport-bounds).
The two assertions have independent inputs: cohomological amplitude in the first,
and bounded constructibility plus a Tor interval in the second. The comparison is
an isomorphism of derived functors on the bounded constructible etale complexes
in the specified interval.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

attribute [local irreducible] Functor.rightDerivedFunctor Functor.mapDerivedCategory
  Functor.rightAdjoint

private theorem etale_plus (P : WeilConjectures.PurityFiniteSetting.{u})
    (T : Scheme.{u}) (K : Etale.DerivedCategoryModule P.Coefficient T)
    (hK : Etale.DerivedCategory.isBoundedConstructible P.Coefficient T K) :
    _root_.DerivedCategory.TStructure.t.plus K := by
  obtain ⟨a, b, _, hv⟩ := hK.2
  exact ⟨a, (_root_.DerivedCategory.isGE_iff K a).mpr
    (fun q hq ↦ hv q (.inl hq))⟩

private noncomputable def closedComparison (P : WeilConjectures.PurityFiniteSetting.{u})
    {Z T : Scheme.{u}}
    [Z.Over (Spec (.of P.field.k))] [T.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of P.field.k))]
    [QuasiCompact (Z ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (T ↘ Spec (.of P.field.k))]
    [QuasiCompact (T ↘ Spec (.of P.field.k))]
    (i : Z ⟶ T) [IsClosedImmersion i] :
    ObjectProperty.ι (Etale.DerivedCategory.isBoundedConstructible P.Coefficient T) ⋙
        finiteCoefficientIntrinsicDerivedComparison T P.Ring ⋙ P.exceptionalInverseImage i ≅
      ObjectProperty.ι (Etale.DerivedCategory.isBoundedConstructible P.Coefficient T) ⋙
        (R(Etale.lowerStar (ModuleCat.{u + 1} P.Coefficient) i)).rightAdjoint ⋙
        finiteCoefficientIntrinsicDerivedComparison Z P.Ring := by
  let E := finiteCoefficientIntrinsicRealization T P.Ring
  have : E.Additive := finiteCoefficientIntrinsicRealization_additive T P.Ring
  have : PreservesFiniteLimits E :=
    finiteCoefficientIntrinsicRealization_preservesFiniteLimits T P.Ring
  have : PreservesFiniteColimits E :=
    finiteCoefficientIntrinsicRealization_preservesFiniteColimits T P.Ring
  have : E.IsEquivalence := (finiteCoefficientIntrinsicRealization_exact T P.Ring).1
  have : E.asEquivalence.functor.Additive := finiteCoefficientIntrinsicRealization_additive T _
  have : E.asEquivalence.inverse.Additive :=
    Functor.additive_of_preserves_binary_products _
  let ed := E.asEquivalence.mapDerivedCategory
  let N := comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) T
  let R := comparisonLowerStar (ModuleCat.{u + 1} P.Coefficient) T
  let Q := Etale.DerivedCategory.isBoundedConstructible P.Coefficient T
  let C := finiteCoefficientIntrinsicDerivedComparison Z P.Ring
  have ec : finiteCoefficientIntrinsicDerivedComparison T P.Ring ⋙ ed.inverse ≅
      N.mapDerivedCategory :=
    Functor.isoWhiskerRight (Functor.mapDerivedCategoryCompIso N E) ed.inverse ≪≫
      Functor.isoWhiskerLeft N.mapDerivedCategory ed.unitIso.symm ≪≫
      Functor.rightUnitor N.mapDerivedCategory
  have hu : IsIso (Functor.whiskerLeft Q.ι
      (derivedComparisonAdjunction (ModuleCat.{u + 1} P.Coefficient) T).unit) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro K
    exact isIso_derivedComparisonAdjunction_unit_app _ T K.obj (etale_plus P T K.obj K.property)
  let eu : Q.ι ⋙ N.mapDerivedCategory ⋙ R.rightDerivedFunctor ≅ Q.ι :=
    (asIso (Functor.whiskerLeft Q.ι
      (derivedComparisonAdjunction (ModuleCat.{u + 1} P.Coefficient) T).unit)).symm
  letI := hasCompactification_of_finiteType_over_field P.field.k Z T i
  let G := Etale.rightDerivedUpperShriek (ModuleCat.{u + 1} P.Coefficient) i
  let eg : G ≅ (R(Etale.lowerStar (ModuleCat.{u + 1} P.Coefficient) i)).rightAdjoint :=
    ((Etale.rightDerivedUpperShriekAdjunction _ i).ofNatIsoLeft
      (Etale.rightDerivedLowerShriekIsoRightDerivedLowerStar _ i)).rightAdjointUniq
        (Adjunction.ofIsLeftAdjoint _)
  change Q.ι ⋙ finiteCoefficientIntrinsicDerivedComparison T P.Ring ⋙
    ed.inverse ⋙ R.rightDerivedFunctor ⋙ G ⋙ C ≅ _
  exact Functor.isoWhiskerRight (Functor.isoWhiskerLeft Q.ι ec)
      (R.rightDerivedFunctor ⋙ G ⋙ C) ≪≫
    Functor.isoWhiskerRight eu (G ⋙ C) ≪≫
    Functor.isoWhiskerLeft Q.ι (Functor.isoWhiskerRight eg C)

private theorem intrinsic_of_iso (P : WeilConjectures.PurityFiniteSetting.{u})
    (T : Scheme.{u}) {K L : Scheme.proEtaleDerivedCategory T P.Ring} (e : K ≅ L)
    (h : Scheme.intrinsicFiniteTorsionConstructible
      P.coefficients.l P.extension P.level P.level_pos T L) :
    Scheme.intrinsicFiniteTorsionConstructible
      P.coefficients.l P.extension P.level P.level_pos T K := by
  constructor
  · apply h.1.subset
    intro q hq hz
    exact hq (hz.of_iso ((_root_.DerivedCategory.homologyFunctor _ q).mapIso e))
  · intro q
    have hc := h.2 q
    rw [Scheme.proEtaleModuleRestriction_constructible_iff] at hc ⊢
    exact isConstructible_of_iso
      ((Scheme.proEtaleModuleRestriction T P.Ring).mapIso
        ((_root_.DerivedCategory.homologyFunctor _ q).mapIso e)).symm hc

private theorem interval_of_iso (P : WeilConjectures.PurityFiniteSetting.{u})
    (T : Scheme.{u}) {K L : Scheme.proEtaleDerivedCategory T P.Ring} (e : K ≅ L)
    (r s : ℤ) (h : WeilConjectures.constructibleInterval
      P.coefficients.l P.extension P.level P.level_pos T r s L) :
    WeilConjectures.constructibleInterval
      P.coefficients.l P.extension P.level P.level_pos T r s K := by
  refine ⟨intrinsic_of_iso P T e h.1, ?_⟩
  intro q hq
  apply h.2
  intro hz
  exact hq (hz.of_iso ((_root_.DerivedCategory.homologyFunctor _ q).mapIso e))

private theorem tor_of_iso (P : WeilConjectures.PurityFiniteSetting.{u})
    (T : Scheme.{u}) {K L : Scheme.proEtaleDerivedCategory T P.Ring} (e : K ≅ L)
    (r s : ℤ) (h : Scheme.HasProEtaleTorAmplitude T P.Ring L r s) :
    Scheme.HasProEtaleTorAmplitude T P.Ring K r s := by
  refine ⟨h.1, ?_⟩
  intro M Q hM f hf hQ N q hq
  exact h.2 M Q (hM.map (fun eM ↦ eM ≪≫ e)) f hf hQ N q hq

private theorem intrinsic_origin (P : WeilConjectures.PurityFiniteSetting.{u})
    (T : Scheme.{u}) (K : Scheme.proEtaleDerivedCategory T P.Ring)
    (hK : Scheme.intrinsicFiniteTorsionConstructible
      P.coefficients.l P.extension P.level P.level_pos T K) :
    ∃ L : Etale.DerivedCategoryModule P.Coefficient T,
      Etale.DerivedCategory.isBoundedConstructible P.Coefficient T L ∧
      Nonempty ((finiteCoefficientIntrinsicDerivedComparison T P.Ring).obj L ≅ K) := by
  have hb : ∃ a b : ℤ, a ≤ b ∧ ∀ q : ℤ, (q < a ∨ b < q) →
      IsZero ((_root_.DerivedCategory.homologyFunctor _ q).obj K) := by
    obtain ⟨a, ha⟩ := hK.1.bddBelow
    obtain ⟨b, hb⟩ := hK.1.bddAbove
    refine ⟨min a b, b, min_le_right _ _, ?_⟩
    intro q hq
    by_contra hz
    rcases hq with hq | hq
    · exact (not_lt_of_ge (ha hz)) (lt_of_lt_of_le hq (min_le_left _ _))
    · exact (not_lt_of_ge (hb hz)) hq
  obtain ⟨L, he⟩ := (Scheme.finiteRing_constructibleDerived_origin T P.Ring).2.2.1 K
    |>.mpr ⟨hK.2, hb⟩
  exact ⟨L.obj, L.property, he⟩

private theorem origin_interval (P : WeilConjectures.PurityFiniteSetting.{u})
    (T : Scheme.{u}) (L : Etale.DerivedCategoryModule P.Coefficient T)
    {K : Scheme.proEtaleDerivedCategory T P.Ring}
    (e : (finiteCoefficientIntrinsicDerivedComparison T P.Ring).obj L ≅ K)
    (r s : ℤ) (hK : WeilConjectures.constructibleInterval
      P.coefficients.l P.extension P.level P.level_pos T r s K) :
    _root_.DerivedCategory.homologyConcentratedIn r s L := by
  have he := (Scheme.finiteRing_constructibleDerived_origin T P.Ring).2.2.2 L r s
  have hv : ∀ q : ℤ, (q < r ∨ s < q) →
      IsZero ((_root_.DerivedCategory.homologyFunctor _ q).obj K) := by
    intro q hq
    by_contra hz
    have hb := hK.2 hz
    rcases hq with hq | hq
    · exact (not_lt_of_ge hb.1) hq
    · exact (not_lt_of_ge hb.2) hq
  have hL := he.mpr fun q hq ↦
    (hv q hq).of_iso ((_root_.DerivedCategory.homologyFunctor _ q).mapIso e)
  exact ⟨(_root_.DerivedCategory.isGE_iff L r).mpr (fun q hq ↦ hL q (.inl hq)),
    (_root_.DerivedCategory.isLE_iff L s).mpr (fun q hq ↦ hL q (.inr hq))⟩

private theorem origin_tor (P : WeilConjectures.PurityFiniteSetting.{u})
    (T : Scheme.{u}) (L : Etale.DerivedCategoryModule P.Coefficient T)
    (hL : Etale.DerivedCategory.isBoundedConstructible P.Coefficient T L)
    {K : Scheme.proEtaleDerivedCategory T P.Ring}
    (e : (finiteCoefficientIntrinsicDerivedComparison T P.Ring).obj L ≅ K)
    (r s : ℤ) (hK : Scheme.HasProEtaleTorAmplitude T P.Ring K r s) :
    Etale.DerivedCategory.hasTorAmplitudeIn P.Coefficient T r s L := by
  let Lplus : _root_.DerivedCategory.Plus
      (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)) :=
    ⟨L, etale_plus P T L hL⟩
  let N := comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) T
  let E := finiteCoefficientIntrinsicRealization T P.Ring
  have : E.Additive := finiteCoefficientIntrinsicRealization_additive T P.Ring
  have : PreservesFiniteLimits E :=
    finiteCoefficientIntrinsicRealization_preservesFiniteLimits T P.Ring
  have : PreservesFiniteColimits E :=
    finiteCoefficientIntrinsicRealization_preservesFiniteColimits T P.Ring
  let ec := (Functor.mapDerivedCategoryCompIso N E).app L
  let ep := E.mapDerivedCategory.mapIso (N.mapDerivedCategoryPlusCompatibility.app Lplus)
  exact (comparison_torAmplitudeIn_iff P.Ring T r s hK.1 Lplus).mpr
    (tor_of_iso P T (ep ≪≫ ec.symm ≪≫ e) r s hK)

/-- The two independent closed-support bounds. The natural isomorphism on the full
bounded constructible etale interval category supplies the identification for every witness
alpha: nu_T^* B_e ≅ B, by composing its component with Ri^!(alpha^{-1}).
There is no Tor hypothesis in the first conjunct. The Tor predicate in the second
conjunct quantifies over all pro-etale module sheaves, without an origin restriction.
Source: main-20261015, thm-pur-general-admissibility.proof.md, Step 2
(blueprint: lem-pur-closed-etale-transport-bounds).

Proof:
1. Use finiteRing_constructibleDerived_origin to choose a bounded constructible etale
witness. Its interval-reflection clause transfers the given cohomological interval to
that witness, without any Tor hypothesis.
2. Unfold the published finite exceptional functor as intrinsic realization inverse,
Rnu_*, the ordinary etale exceptional adjoint, and intrinsic comparison. The derived
realization equivalence cancels its inverse. The canonical comparison unit is invertible
on bounded-below etale complexes; whisker its inverse by the remaining functors.
For closed i, the proper forget-supports isomorphism identifies Ri_! with Ri_*;
uniqueness of right adjoints therefore identifies the ordinary exceptional adjoint with
the chosen right adjoint of Ri_*. These natural isomorphisms compose on the full bounded
constructible subcategory and restrict to each interval subcategory.
3. Apply etaleClosedOutput_bounds(a) to the witness. Compose the component of the natural
comparison with Ri^!(alpha^{-1}) to identify its output with Ri^!B. Transport intrinsic
constructibility and cohomological support along this isomorphism.
4. Independently, comparison_torAmplitudeIn_iff reflects the pro-etale Tor interval
for every bounded constructible witness. The exact-derived composition and bounded-below
compatibility isomorphisms identify its comparison with the specified intrinsic one.
No additional coefficient-prime invertibility hypothesis is needed for this lemma.
5. Apply etaleClosedOutput_bounds(b) to one such witness. Transfer constructibility
along the same isomorphism. For Tor amplitude, compose every representative isomorphism
with it; the identical K-flat resolution and arbitrary pro-etale module-sheaf tests then
satisfy the required vanishing. No origin restriction is imposed on the test sheaf. -/
theorem closedEtaleTransport_bounds (P : WeilConjectures.PurityFiniteSetting.{u})
    {Z T W : Scheme.{u}}
    [Z.Over (Spec (.of P.field.k))] [T.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of P.field.k))]
    [QuasiCompact (Z ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (T ↘ Spec (.of P.field.k))]
    [QuasiCompact (T ↘ Spec (.of P.field.k))]
    (i : Z ⟶ T) [IsClosedImmersion i] [i.IsOver (Spec (.of P.field.k))]
    (j : W ⟶ T) [IsOpenImmersion j] [QuasiCompact j]
    (_hij : Set.range i.base = (Set.range j.base)ᶜ)
    (c : ℕ) (_hc : Scheme.HasOpenComplementCondition P.Coefficient j c)
    (r s : ℤ) (_hrs : r ≤ s) :
    (Nonempty
      (ObjectProperty.ι
          (Etale.DerivedCategory.isBoundedConstructible P.Coefficient T ⊓
            _root_.DerivedCategory.homologyConcentratedIn r s) ⋙
          finiteCoefficientIntrinsicDerivedComparison T P.Ring ⋙ P.exceptionalInverseImage i ≅
        ObjectProperty.ι
          (Etale.DerivedCategory.isBoundedConstructible P.Coefficient T ⊓
            _root_.DerivedCategory.homologyConcentratedIn r s) ⋙
          (R(Etale.lowerStar (ModuleCat.{u + 1} P.Coefficient) i)).rightAdjoint ⋙
          finiteCoefficientIntrinsicDerivedComparison Z P.Ring) ∧
      ∀ B : WeilConjectures.intrinsicConstructibleIntervalCategory
          P.coefficients.l P.extension P.level P.level_pos T r s,
        (∃ B_e : Etale.DerivedCategoryModule P.Coefficient T,
          Etale.DerivedCategory.isBoundedConstructible P.Coefficient T B_e ∧
          _root_.DerivedCategory.homologyConcentratedIn r s B_e ∧
          Nonempty ((finiteCoefficientIntrinsicDerivedComparison T P.Ring).obj B_e ≅ B.obj)) ∧
        WeilConjectures.constructibleInterval
          P.coefficients.l P.extension P.level P.level_pos Z r (s + (c : ℤ) + 1)
          ((P.exceptionalInverseImage i).obj B.obj)) ∧
    (∀ B : Scheme.proEtaleDerivedCategory T P.Ring,
      Scheme.intrinsicFiniteTorsionConstructible
        P.coefficients.l P.extension P.level P.level_pos T B →
      Scheme.HasProEtaleTorAmplitude T P.Ring B r s →
      (∀ B_e : Etale.DerivedCategoryModule P.Coefficient T,
        Etale.DerivedCategory.isBoundedConstructible P.Coefficient T B_e →
        Nonempty ((finiteCoefficientIntrinsicDerivedComparison T P.Ring).obj B_e ≅ B) →
        Etale.DerivedCategory.hasTorAmplitudeIn P.Coefficient T r s B_e) ∧
      Scheme.intrinsicFiniteTorsionConstructible
        P.coefficients.l P.extension P.level P.level_pos Z
        ((P.exceptionalInverseImage i).obj B) ∧
      Scheme.HasProEtaleTorAmplitude Z P.Ring ((P.exceptionalInverseImage i).obj B)
        r (s + (c : ℤ) + 1)) := by
  classical
  let Q := Etale.DerivedCategory.isBoundedConstructible P.Coefficient T
  let e := closedComparison P i
  have ei (L : Etale.DerivedCategoryModule P.Coefficient T) (hL : Q L)
      (B : Scheme.proEtaleDerivedCategory T P.Ring)
      (alpha : (finiteCoefficientIntrinsicDerivedComparison T P.Ring).obj L ≅ B) :
      (P.exceptionalInverseImage i).obj B ≅
        (finiteCoefficientIntrinsicDerivedComparison Z P.Ring).obj
          ((R(Etale.lowerStar (ModuleCat.{u + 1} P.Coefficient) i)).rightAdjoint.obj L) :=
    ((P.exceptionalInverseImage i).mapIso alpha).symm ≪≫ e.app ⟨L, hL⟩
  constructor
  · refine ⟨⟨?_⟩, ?_⟩
    · exact Functor.isoWhiskerLeft (ObjectProperty.ιOfLE
        (show Q ⊓ _root_.DerivedCategory.homologyConcentratedIn r s ≤ Q from
          fun _ h ↦ h.1)) e
    · intro B
      obtain ⟨L, hL, ⟨alpha⟩⟩ := intrinsic_origin P T B.obj B.property.1
      have hLint := origin_interval P T L alpha r s B.property
      refine ⟨⟨L, hL, hLint, ⟨alpha⟩⟩, ?_⟩
      exact interval_of_iso P Z (ei L hL B.obj alpha) r (s + (c : ℤ) + 1)
        ((etaleClosedOutput_bounds P i j _hij c _hc L hL r s _hrs).1 hLint).2
  · intro B hB hTor
    have hreflect : ∀ L : Etale.DerivedCategoryModule P.Coefficient T,
        Q L → Nonempty ((finiteCoefficientIntrinsicDerivedComparison T P.Ring).obj L ≅ B) →
        Etale.DerivedCategory.hasTorAmplitudeIn P.Coefficient T r s L := by
      rintro L hL ⟨alpha⟩
      exact origin_tor P T L hL alpha r s hTor
    refine ⟨hreflect, ?_⟩
    obtain ⟨L, hL, ⟨alpha⟩⟩ := intrinsic_origin P T B hB
    have hout := ((etaleClosedOutput_bounds P i j _hij c _hc L hL r s _hrs).2
      (hreflect L hL ⟨alpha⟩)).2
    exact ⟨intrinsic_of_iso P Z (ei L hL B alpha) hout.1,
      tor_of_iso P Z (ei L hL B alpha) r (s + (c : ℤ) + 1) hout.2⟩

end AlgebraicGeometry.ProEtale
