/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CanonicalTate.CanonicalTateComplexComparisons
import WeilConjectures.SixFunctors.Integral.IntegralPullbackAugmentationAmbient
import WeilConjectures.SmoothPurity.Sf.SfDerivedCompleteLegacyComparison
import WeilConjectures.SixFunctors.Supporting.RoosIntrinsicCompletenessEquivalence
import WeilConjectures.DeligneLaumon.PrincipalKoszulStrictReplacement.PrincipalKoszulStrictReplacement
import Mathlib.Data.Nat.Prime.Infinite

/-! # Canonical Tate comparisons: CompletedComparisons

Source: current blueprint, def-pur-tate-datum, canonical root-line comparisons.
This module preserves the original unshifted comparison declarations.
(blueprint: def-pur-canonical-tate-completed-comparisons).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option Elab.async false
universe u v a b c d
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped TensorProduct ChangeOfRings
namespace WeilConjectures.CanonicalTate
open FrobeniusCoefficientTwists

attribute [local instance 5000] integralTowerHasDerivedCategory scalarReductionTargetDerived

attribute [-instance] PrincipalKoszulStrictReplacement.abSheafify
  PrincipalKoszulStrictReplacement.abLocallyBijective
  PrincipalKoszulStrictReplacement.siteSmall
attribute [local irreducible] IntegralOnSlice.completion
  IntegralOnSlice.completionComparison IntegralOnSlice.completionUnit
  IntegralOnSlice.duality IntegralOnSlice.roosUnit IntegralAmbient.tensorTowerIso
  HasDerivedCategory.standard completedIntegralCoefficientSheafUnrestricted
  coefficientTotalTensor SheafOfModules.monoidalCategory IntegralOnSlice.tower
  IntegralOnSlice.augmentation integralOperationsTensorTowerFunctor

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
private theorem roosUnit_isIso_of_complete (X : Scheme.{u})
    (T : CochainComplex (integralTowerModules l E X) ℤ)
    (hT : IntegralOnSlice.Good l E X none T)
    (hc : IsSfDerivedComplete l E X (DerivedCategory.Q.obj T)) :
    IsIso (DerivedCategory.Q.map (IntegralOnSlice.roosUnit l E X none T)) := by
  obtain ⟨p, hlp, hp⟩ := Nat.exists_infinite_primes (l + 1)
  let : Fact p.Prime := ⟨hp⟩
  let D : FiniteFieldDatum.{0} :=
    { p := p
      a := 1
      q := p
      prime := hp
      exponent_pos := le_rfl
      cardinality_eq := by simp
      k₀ := ZMod p
      card_base := by simp [Nat.card_eq_fintype_card]
      k := AlgebraicClosure (ZMod p) }
  have hl : l ≠ D.p := Nat.ne_of_lt (Nat.lt_of_succ_le hlp)
  have hcomplete :
      IntegralOnSlice.IsComplete l E X none (DerivedCategory.Q.obj T) :=
    ⟨D, hl, (sfDerivedComplete_iff_legacy l E X D hl _).mp hc⟩
  obtain ⟨datum, hdatum, _⟩ := PrincipalKoszulStrictReplacement.coefficient_datum l E
  let TG : (IntegralOnSlice.Good l E X none).FullSubcategory := ⟨T, hT⟩
  have hu : IsIso ((IntegralOnSlice.completionUnit l E X none).app
      (DerivedCategory.Q.obj T)) :=
    ((roosIntrinsicCompletenessEquivalence.{u, u} p l (by omega) E X datum hdatum
      (DerivedCategory.Q.obj T) TG (Iso.refl _)).out 0 4).mp hcomplete
  have hn : (IntegralOnSlice.completionUnit l E X none).app
      ((IntegralOnSlice.qGood l E X none).obj TG) ≫
        (IntegralOnSlice.completionComparison l E X none).hom.app TG =
      DerivedCategory.Q.map (IntegralOnSlice.roosUnit l E X none TG.obj) := by
    unfold IntegralOnSlice.completionUnit
    exact (IntegralOnSlice.completionUnit_existsUnique l E X none).exists.choose_spec TG
  exact
    hn ▸ IsIso.comp_isIso' hu
      (NatIso.hom_app_isIso (IntegralOnSlice.completionComparison l E X none) TG)

section TensorCompletion
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

end TensorCompletion

/-- The integral pullback augmentation is invertible on unshifted root lines.
Source: blueprint def-pur-tate-datum, canonical roots and tensor powers
(blueprint: def-pur-canonical-tate-completed-comparisons).
Proof: The ordinary pullback comparison identifies the ambient representative
with the integral single line on X. Its constructibility gives completeness.
The normalized Roos completeness criterion makes its completion unit invertible.
The representative normalization and the tower comparison then make the ambient
operation unit invertible. The specified augmentation equals that unit composed
with the termwise ordinary pullback comparison, including its zero Roos component. -/
theorem integralPullUnit_isIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] (r : ℕ) :
    IsIso (DerivedCategory.Q.map ((pullbackAugmentation l E f).app
      (integralComplex l E Y r))) := by
  let : (show integralTowerModules l E Y ⥤ integralTowerModules l E X from
      FrobeniusCoefficientTwists.modulePull l E f).PreservesZeroMorphisms :=
    @Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _
      (show integralTowerModules l E Y ⥤ integralTowerModules l E X from
        FrobeniusCoefficientTwists.modulePull l E f)
      (proEtaleRingModulePullback_additive f
        ((PurCompactSupport.completed l E).ring Y)
        ((PurCompactSupport.completed l E).ring X)
        ((PurCompactSupport.completed l E).pull f))
  let : (IntegralAmbient.pull l E f).PreservesZeroMorphisms :=
    @Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _
      (IntegralAmbient.pull l E f) (IntegralAmbient.pull_additive l E f)
  obtain ⟨b, hb⟩ := integralPullbackAugmentation_ambient l E f
  let P := integralComplex l E Y r
  let M := (IntegralAmbient.pullComplex l E f).obj P
  have hM : IntegralOnSlice.Good l E X none M :=
    IntegralAmbient.pull_good l E f P (integralGood l E Y r)
  let eM : M ≅ integralComplex l E X r :=
    ((NatIso.mapHomologicalComplex b (.up ℤ)).app P).symm ≪≫
      ((HomologicalComplex.singleMapHomologicalComplex
        (FrobeniusCoefficientTwists.modulePull l E f) (.up ℤ) 0).app
        (FrobeniusCoefficientTwists.positiveLine l E Y r)) ≪≫
      ((HomologicalComplex.single _ (.up ℤ) 0).mapIso
        (sfOrientationIntegralLineMaps l E f r))
  have hc : IsSfDerivedComplete l E X (DerivedCategory.Q.obj M) :=
    ((sfIntegralConstructible l E X).prop_of_iso
      (DerivedCategory.Q.mapIso eM).symm
      (sfIntegralTwistingObject_mem l E X (r : ℤ))).1
  have hr := roosUnit_isIso_of_complete l E X M hM hc
  have hmap : IsIso (DerivedCategory.Q.map
      (integralOperationsRoosFunctor.map ((IntegralAmbient.pullTowerIso l E f).hom.app P))) :=
    (DerivedCategory.Q.mapIso (integralOperationsRoosFunctor.mapIso
      ((IntegralAmbient.pullTowerIso l E f).app P))).isIso_hom
  have ha : IsIso (DerivedCategory.Q.map (IntegralAmbient.pullOperationUnit l E f P)) := by
    set_option backward.isDefEq.respectTransparency true in
    set_option backward.isDefEq.respectTransparency.types true in
    exact isIso_map_comp_of_isIso_maps
      (DerivedCategory.Q (C := integralTowerModules l E X))
      (IntegralOnSlice.roosUnit l E X none M)
      (integralOperationsRoosFunctor.map ((IntegralAmbient.pullTowerIso l E f).hom.app P))
      hr hmap
  have hi : IsIso (DerivedCategory.Q.map
      ((NatIso.mapHomologicalComplex b (.up ℤ)).hom.app P)) :=
    (DerivedCategory.Q.mapIso ((NatIso.mapHomologicalComplex b (.up ℤ)).app P)).isIso_hom
  rw [hb P]
  set_option backward.isDefEq.respectTransparency true in
  set_option backward.isDefEq.respectTransparency.types true in
  exact isIso_map_comp_of_isIso_maps
    (DerivedCategory.Q (C := integralTowerModules l E X))
    ((NatIso.mapHomologicalComplex b (.up ℤ)).hom.app P)
    (IntegralAmbient.pullOperationUnit l E f P) hi ha

end WeilConjectures.CanonicalTate
