/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NZ
-/
module

public import Sheaf.Paper.CanonicalTateComplexComparisons
import Sheaf.Paper.IntegralPullbackAugmentationAmbient
import Sheaf.Paper.SfDerivedCompleteLegacyComparison
import Sheaf.Paper.RoosIntrinsicCompletenessEquivalence
import Sheaf.Paper.PrincipalKoszulStrictReplacement
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
private theorem isIso_map_comp_of_isIso_maps
    {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D)
    {A B C' : C} (f : A ⟶ B) (g : B ⟶ C')
    (hf : IsIso (F.map f)) (hg : IsIso (F.map g)) : IsIso (F.map (f ≫ g)) := by
  rw [F.map_comp]
  exact IsIso.comp_isIso' hf hg

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

/-- The ordinary product of two integral lines is already complete.
Source: blueprint def-pur-tate-datum, canonical roots and tensor powers
(blueprint: def-pur-canonical-tate-completed-comparisons).
Proof: tensor_good gives a flat-term K-flat model. The normalized product
identifies it with the intrinsically complete line of exponent r+s. The legacy
comparison and Roos completeness criterion make its actual completion unit
invertible. The representative normalization then makes Q(roosUnit) invertible.
The tensor operation unit composes this map with the Roos image of tensorTowerIso,
so localization makes that specified operation unit invertible. -/
theorem integralTensorUnit_isIso (X : Scheme.{u})
    [∀ x : X, Invertible (l : X.residueField x)] (r s : ℕ) :
    IsIso (DerivedCategory.Q.map (IntegralAmbient.tensorOperationUnit l E X
      (integralComplex l E X r) (integralComplex l E X s))) := by
  let P := integralComplex l E X r
  let Q := integralComplex l E X s
  let T : CochainComplex (integralTowerModules l E X) ℤ :=
    (coefficientTotalTensor.{u, u + 1, u} (ProEt.topology X)
    (completedIntegralCommRingSheafUnrestricted l E X)).obj (P, Q)
  have hT : IntegralOnSlice.Good.{u, u} l E X none T :=
    IntegralAmbient.tensor_good.{u, u} l E X P Q
      (integralGood l E X r)
      (integralGood l E X s)
  have hc : IsSfDerivedComplete l E X (DerivedCategory.Q.obj T) :=
    ((sfIntegralConstructible l E X).prop_of_iso
      (DerivedCategory.Q.mapIso (integralProductComplex l E X r s)).symm
      (sfIntegralTwistingObject_mem l E X ((r + s : ℕ) : ℤ))).1
  have hr := roosUnit_isIso_of_complete l E X T hT hc
  have hmap : IsIso (DerivedCategory.Q.map
      (integralOperationsRoosFunctor.map
        ((IntegralAmbient.tensorTowerIso l E X).hom.app (P, Q)))) :=
    (DerivedCategory.Q.mapIso
      (integralOperationsRoosFunctor.mapIso
        ((IntegralAmbient.tensorTowerIso l E X).app (P, Q)))).isIso_hom
  set_option backward.isDefEq.respectTransparency true in
  set_option backward.isDefEq.respectTransparency.types true in
  exact isIso_map_comp_of_isIso_maps
    (DerivedCategory.Q (C := integralTowerModules l E X))
    (IntegralOnSlice.roosUnit l E X none T)
    (integralOperationsRoosFunctor.map
      ((IntegralAmbient.tensorTowerIso l E X).hom.app (P, Q))) hr hmap

end TensorCompletion

/-- The integral tensor-power identification on the published completed tensor.
Source: blueprint def-pur-tate-datum, canonical roots and tensor powers
(blueprint: def-pur-canonical-tate-completed-comparisons). -/
def integralProduct (X : Scheme.{u})
    [∀ x : X, Invertible (l : X.residueField x)] (r s : ℕ) :
    (integralCompletedTensor l E X).obj
        (sfIntegralTwistingObject l E X (r : ℤ),
          sfIntegralTwistingObject l E X (s : ℤ)) ≅
      sfIntegralTwistingObject l E X ((r + s : ℕ) : ℤ) :=
  (integralCompletedTensorComparison l E X).app
      (⟨integralComplex l E X r, integralGood l E X r⟩,
        ⟨integralComplex l E X s, integralGood l E X s⟩) ≪≫
    (@asIso _ _ _ _ (DerivedCategory.Q.map (IntegralAmbient.tensorOperationUnit l E X
      (integralComplex l E X r) (integralComplex l E X s)))
        (integralTensorUnit_isIso l E X r s)).symm ≪≫
    DerivedCategory.Q.mapIso (integralProductComplex l E X r s)

/-- The finite tensor-power identification on the intrinsic derived tensor.
Source: blueprint def-pur-tate-datum, canonical roots and tensor powers
(blueprint: def-pur-canonical-tate-completed-comparisons). -/
def finiteProduct (X : Scheme.{u})
    [∀ x : X, Invertible (l : X.residueField x)] (n r s : ℕ) :
    (finiteIntrinsicDerivedTensor l E X n).obj
        (DerivedCategory.Q.obj (finiteComplex l E X n r),
          DerivedCategory.Q.obj (finiteComplex l E X n s)) ≅
      DerivedCategory.Q.obj (finiteComplex l E X n (r + s)) :=
  (CoefficientTensorModels.iso (ProEt.topology X)
      (integralCoefficientCommRingSheaf l E X n)
      (finiteIntrinsicClosed l E X n) (finiteIntrinsicTensorModels l E X n)
      (finiteComplex l E X n r) (finiteComplex l E X n s)
      (finiteGood l E X n r) (finiteGood l E X n s)).symm ≪≫
    DerivedCategory.Q.mapIso (finiteProductComplex l E X n r s)

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

/-- The canonical integral twist pullback comparison, from the actual Roos augmentation.
Source: blueprint def-pur-tate-datum, canonical roots and tensor powers
(blueprint: def-pur-canonical-tate-completed-comparisons). -/
def integralPull {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] (r : ℕ) :
    (integralDerivedPullback l E f).obj (sfIntegralTwistingObject l E Y (r : ℤ)) ≅
      sfIntegralTwistingObject l E X (r : ℤ) :=
  (integralDerivedPullbackComparison l E f).app
      ⟨integralComplex l E Y r, integralGood l E Y r⟩ ≪≫
    (@asIso _ _ _ _ (DerivedCategory.Q.map ((pullbackAugmentation l E f).app
      (integralComplex l E Y r))) (integralPullUnit_isIso l E f r)).symm ≪≫
    DerivedCategory.Q.mapIso
      ((HomologicalComplex.singleMapHomologicalComplex (modulePull l E f) (.up ℤ) 0).app
        (positiveLine l E Y r)) ≪≫
    DerivedCategory.Q.mapIso ((HomologicalComplex.single _ (.up ℤ) 0).mapIso
      (sfOrientationIntegralLineMaps l E f r))

end WeilConjectures.CanonicalTate
