/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Reduction.FiniteReductionTensorFactors

import all WeilConjectures.AlgebraicGeometry.Reduction.ReductionDirectImage
import all WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothLevelOfOrientation
import all WeilConjectures.AlgebraicGeometry.Etale.ProEtale.EtaleProEtaleExceptionalObjectComparison
import WeilConjectures.AlgebraicGeometry.Cohomological.CohomologicalSmoothnessFiniteComparison

/-! # Constructibility of the reduced theta source

The source of the coefficient theta map is a finite-Tor constructible object.
This is the domain fact needed to restrict the reduced exceptional counit
adjunction to the Hom set used by the theta-factor argument.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting
private theorem native_ctf_iff (A : Type (u + 1)) [CommRing A] [Finite A]
    (T : Scheme.{u}) (K : Etale.FiniteSmoothPurity.proCategory A T) :
    Etale.FiniteSmoothPurity.IsCtf A T K ↔
      ProEtale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) T K := by
  constructor
  · intro h
    obtain ⟨a, b, _, hv⟩ := h.2.1
    have hb : _root_.DerivedCategory.TStructure.t.bounded K :=
      ⟨⟨a, (_root_.DerivedCategory.isGE_iff K a).mpr
        (fun i hi ↦ hv i (Or.inl hi))⟩,
        ⟨b, (_root_.DerivedCategory.isLE_iff K b).mpr
          (fun i hi ↦ hv i (Or.inr hi))⟩⟩
    refine ⟨ProEtale.DerivedCategory.boundedConstructible_of_homology _ hb
      (fun i ↦ ProEtale.exists_isConstructibleSheaf_iso_comparisonUpperStar_obj _
        ((ProEtale.fixed_constructible_iff _ T _).mp (h.1 i))), ?_⟩
    obtain ⟨c, e, _, ht⟩ := h.2.2
    exact ⟨c, e, ht⟩
  · intro h
    have hc := ProEtale.DerivedCategory.boundedConstructible_le_boundedConstructibleIntrinsic
      _ h.1
    refine ⟨fun i ↦ (ProEtale.fixed_constructible_iff _ T _).mpr (hc.2 i), ?_, ?_⟩
    · obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := hc.1
      refine ⟨min a b, b, min_le_right _ _, fun i hi ↦ ?_⟩
      rcases hi with hi | hi
      · exact (_root_.DerivedCategory.isGE_iff _ a).mp ha i
          (lt_of_lt_of_le hi (min_le_left _ _))
      · exact (_root_.DerivedCategory.isLE_iff _ b).mp hb i hi
    · obtain ⟨a, b, ht⟩ := h.2
      exact ⟨min a b, max a b, min_le_max,
        ht.mono (min_le_left _ _) (le_max_right _ _)⟩

section Morphism
variable (P : PurityFiniteSetting.{u}) (m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ P.level)
variable {X Y : Scheme.{u}}
variable [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
variable [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
variable [QuasiCompact (X ↘ Spec (.of P.field.k))]
variable [IsSeparated (X ↘ Spec (.of P.field.k))]
variable [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
variable [QuasiCompact (Y ↘ Spec (.of P.field.k))]
variable [IsSeparated (Y ↘ Spec (.of P.field.k))]
variable (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
variable [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]

set_option linter.unusedSectionVars false in
/-- The reduced tensor source used by theta is finite-Tor constructible.
Source: blueprint/latest, thm-pur-finite-reduction-of-purity, Step 2
(blueprint: lem-pur-finite-reduction-theta-factor-source-ctf).

Proof: the bounded finite-Tor model theorem gives an etale origin for the
pullback of the finite-Tor constructible object `K`.  The finite smooth tensor
domain theorem applies to that origin and the diagonal dualizing complex;
transporting its constructibility through the intrinsic comparison and then
through finite scalar reduction gives the displayed reduced source.  The
reduction functor preserves the recorded Tor interval by
`finiteReduction_preserves_ctf`, so the result is exactly the predicate needed
by the restricted exceptional adjunction.  No witness object is chosen by the
statement: all transports act on the displayed canonical source.
-/
theorem finiteReduction_thetaFactor_source_ctf
    (d : ℕ) [SmoothOfRelativeDimension d f]
    (K : Scheme.proEtaleDerivedCategory Y P.Ring)
    (hK : finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos Y K) :
    letI := hasCompactification_of_finiteType_over_field P.field.k X Y f
    finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos X
      ((Scheme.sfIntrinsicDerivedEquivalence X P.Ring).functor.obj
        (((smoothPurityTensor P.Coefficient X).obj
          ((P.smoothPurityPullback f).obj
            ((Scheme.sfIntrinsicDerivedEquivalence Y P.Ring).inverse.obj K))).obj
          (P.diagonalDualizing f))) := by
  classical
  let := hasCompactification_of_finiteType_over_field P.field.k X Y f
  let := isNoetherian_of_locallyOfFiniteType (X ↘ Spec (.of P.field.k))
  let := isNoetherian_of_locallyOfFiniteType (Y ↘ Spec (.of P.field.k))
  let E := Scheme.sfIntrinsicDerivedEquivalence Y P.Ring
  let M := E.inverse.obj K
  have hgood : ProEtale.ReductionGood Y P.Ring (E.functor.obj M) :=
    ProEtale.reductionGood_iso (E.counitIso.app K).symm ⟨hK.1.1, hK.1.2, hK.2⟩
  have hM := (native_ctf_iff P.Coefficient Y M).mpr
    ((ProEtale.reductionGood_realization_iff Y P.Ring M).mp hgood)
  let := P.finiteComparedInvertibleExponent (Y ↘ Spec (.of P.field.k))
  obtain ⟨N, hN, hA, hu⟩ :=
    HasInvertibleExponent.exists_isUnit_natCast (Λ := P.Coefficient) (X := Y)
  have hY (y : Y) : IsUnit (N : Y.presheaf.stalk y) := by
    simpa only [map_natCast] using hu.map (Y.presheaf.germ ⊤ y trivial).hom
  let L := P.diagonalOrdinaryDualizing f
  let alpha : Etale.dualizingComplex P.Coefficient f ≅ L :=
    (Etale.rightDerivedUpperShriek P.Coefficient f).mapIso
      (smoothPurityUnitIso P.Coefficient Y).symm
  have hs := (Etale.FiniteSmoothPurity.proObjectsCtf P.Coefficient
    N hN hA f d hY L alpha M hM).1
  let ePull := (ProEtale.leftDerivedUpperStarIsoMapDerivedCategory
    (ModuleCat.{u + 1} P.Coefficient) f).app M
  let eSource :=
    ((smoothPurityTensor P.Coefficient X).mapIso ePull.symm).app
        (P.diagonalDualizing f) ≪≫
      ((smoothPurityTensor P.Coefficient X).obj
        ((Etale.FiniteSmoothPurity.proPullback P.Coefficient f).obj M)).mapIso
          (P.diagonalDualizingComparison f)
  have hsource := Etale.FiniteSmoothPurity.isCtfOfIso P.Coefficient X eSource.symm hs
  have hreal := (ProEtale.reductionGood_realization_iff X P.Ring _).mpr
    ((native_ctf_iff P.Coefficient X _).mp hsource)
  exact ⟨⟨hreal.1, hreal.2.1⟩, hreal.2.2⟩

end Morphism
end WeilConjectures.PurityFiniteSetting
