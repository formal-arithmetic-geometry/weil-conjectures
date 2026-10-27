/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NZ
-/
module

public import Sheaf.Paper.FrobeniusCoefficientTwistsCanonical
public import Sheaf.SixFunctors.SchemeGeometricFrobenius
public import Sheaf.Paper.CartesianCoefficientTwists
public import Sheaf.Paper.IntegralOperationsScalarComparisons
public import Sheaf.Paper.OrientationIntegralCoefficientTwists
public import Sheaf.Paper.IntegralTwistBaseChange
public import Sheaf.Paper.SignedTwistReductionComparison
public import Sheaf.Paper.CanonicalTateCommonComparisons
import Sheaf.Paper.SfDerivedDirectImage
import Sheaf.Paper.PrincipalKoszulStrictReplacement

/-! # Canonical Tate reduction comparisons

Source: current blueprint, def-pur-tate-datum, canonical root-line comparisons.
This module preserves the original unshifted comparison declarations.
(blueprint: def-pur-canonical-tate-comparisons).
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

attribute [local irreducible] proEtaleRingModulePullback proEtaleRingModuleAdjunction
private local instance (X : Scheme.{u}) : EssentiallySmall.{u + 1} X.ProEt :=
  essentiallySmallSelf.{0, u, u + 1} _

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
/-- The finite reduction model using the prescribed universal counit.
Source: Stacks 06YY, coefficient reduction
(blueprint: def-pur-canonical-tate-comparisons). -/
def reductionModel (X : Scheme.{u}) (n : ℕ)
    (P : CochainComplex (integralTowerModules l E X) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      (J := ProEt.topology X) (R := completedIntegralCommRingSheafUnrestricted l E X) P) :
    (scalarReductionDerivedExtension l E X n).obj (DerivedCategory.Q.obj P) ≅
      DerivedCategory.Q.obj (((scalarReductionExtension l E X n).mapHomologicalComplex
        (.up ℤ)).obj P) := by
  letI : IsIso ((scalarReductionCounit l E X n).app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) :=
    (scalarReductionDerivedExistence l E X n).choose_spec.choose_spec.2.2 P hP
  exact (scalarReductionDerivedExtension l E X n).mapIso
      ((DerivedCategory.quotientCompQhIso _).app P).symm ≪≫
    asIso ((scalarReductionCounit l E X n).app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) ≪≫
    (DerivedCategory.quotientCompQhIso _).app _

/-- The ordinary reduction/pullback comparison is fixed by both actual units.
Source: blueprint coefficient balancing before realization
(blueprint: def-pur-canonical-tate-comparisons).
Proof: pullback and scalar extension are left adjoints to the same composite
restriction/direct-image functor. On source sections both units insert the unit
scalar. Associativity of tensor balancing sends these two nested units to each
other, giving the indicated isomorphism. The adjunction bijections make its
normalization determine it uniquely. -/
theorem ordinaryReductionSquare_existsUnique {X Y : Scheme.{u}} (g : X ⟶ Y) (n : ℕ) :
    ∃! e : modulePull l E g ⋙ scalarReductionExtension l E X n ≅
        scalarReductionExtension l E Y n ⋙ finiteModulePull l E g n,
      ∀ (M : integralTowerModules l E Y) (V : Y.ProEt) (x : M.val.obj (op V)),
        (e.hom.app M).val.app (op ((proEtaleBaseChange g).obj V))
          (((scalarReductionExtension_adjunction l E X n).choose.unit.app
            ((modulePull l E g).obj M)).val.app (op ((proEtaleBaseChange g).obj V))
              (moduleSection l E g M V x)) =
        finiteModuleSection l E g n ((scalarReductionExtension l E Y n).obj M) V
          (((scalarReductionExtension_adjunction l E Y n).choose.unit.app M).val.app
            (op V) x) := by
  let a₀ := proEtaleRingModuleAdjunction g
    ((PurCompactSupport.completed l E).ring Y)
    ((PurCompactSupport.completed l E).ring X) ((PurCompactSupport.completed l E).pull g)
  let b₀ := proEtaleRingModuleAdjunction g
    ((PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)).ring Y)
    ((PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)).ring X)
    ((PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)).pull g)
  have hi : proEtaleRingDirectImageMap g
      ((PurCompactSupport.completed l E).ring Y)
      ((PurCompactSupport.completed l E).ring X) ((PurCompactSupport.completed l E).pull g) =
        sfCompletedCoefficientMap l E g :=
    ((proEtaleSheafAdjunction g CommRingCat.{u + 1}).homEquiv _ _).apply_symm_apply _
  have hf : proEtaleRingDirectImageMap g
      ((PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)).ring Y)
      ((PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)).ring X)
      ((PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)).pull g) =
        proEtaleCoefficientDirectImageMap g (Padic.coefficientExtensionRing l E (n + 1)) :=
    ((proEtaleSheafAdjunction g CommRingCat.{u + 1}).homEquiv _ _).apply_symm_apply _
  let i : proEtaleRingModuleDirectImage g
      ((PurCompactSupport.completed l E).ring Y)
      ((PurCompactSupport.completed l E).ring X) ((PurCompactSupport.completed l E).pull g) ≅
        sfCompletedModuleDirectImage l E g :=
    SheafOfModules.pushforwardCongr (by rw [hi])
  let j : proEtaleRingModuleDirectImage g
      ((PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)).ring Y)
      ((PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)).ring X)
      ((PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)).pull g) ≅
        proEtaleConstantModuleDirectImage g (Padic.coefficientExtensionRing l E (n + 1)) :=
    SheafOfModules.pushforwardCongr (by rw [hf])
  let a := a₀.ofNatIsoRight i
  let b := b₀.ofNatIsoRight j
  let x := (scalarReductionExtension_adjunction l E X n).choose
  let y := (scalarReductionExtension_adjunction l E Y n).choose
  let d := (sfDirectImageRestrictionComparison_existsUnique l E g n).exists.choose
  have hd (N : normalizedDVRModules l E X n) (V : Y.ProEtᵒᵖ)
      (z : N.val.obj ((proEtaleBaseChange g).op.obj V)) :
      (d.hom.app N).val.app V z = z :=
    (sfDirectImageRestrictionComparison_existsUnique l E g n).exists.choose_spec N V z
  have hdi (N : normalizedDVRModules l E X n) (V : Y.ProEtᵒᵖ)
      (z : N.val.obj ((proEtaleBaseChange g).op.obj V)) :
      (d.inv.app N).val.app V z = z := by
    have h := congrArg (fun t ↦ t.val.app V z) (d.inv_hom_id_app N)
    change (d.hom.app N).val.app V ((d.inv.app N).val.app V z) = z at h
    rw [hd] at h
    exact h
  let adj₁ := (a.comp x).ofNatIsoRight d.symm
  let adj₂ := y.comp b
  let e : modulePull l E g ⋙ scalarReductionExtension l E X n ≅
      scalarReductionExtension l E Y n ⋙ finiteModulePull l E g n :=
    adj₁.leftAdjointUniq adj₂
  have he (M : integralTowerModules l E Y) (V : Y.ProEt) (z : M.val.obj (op V)) :=
    congrArg (fun t ↦ t.val.app (op V) z) (adj₁.unit_leftAdjointUniq_hom_app adj₂ M)
  have hu₁ (M : integralTowerModules l E Y) (V : Y.ProEt) (z : M.val.obj (op V)) :
      (adj₁.unit.app M).val.app (op V) z =
        (x.unit.app ((modulePull l E g).obj M)).val.app
          (op ((proEtaleBaseChange g).obj V)) (moduleSection l E g M V z) := by
    simp only [adj₁, Adjunction.ofNatIsoRight_unit, NatTrans.comp_app,
      Functor.whiskerLeft_app, Iso.symm_hom, Functor.comp_obj,
      Adjunction.comp_unit_app]
    change (d.inv.app _).val.app (op V)
      ((i.hom.app _).val.app (op V)
        ((x.unit.app _).val.app _ (moduleSection l E g M V z))) = _
    rw [hdi]
    rfl
  have hu₂ (M : integralTowerModules l E Y) (V : Y.ProEt) (z : M.val.obj (op V)) :
      (adj₂.unit.app M).val.app (op V) z =
        finiteModuleSection l E g n ((scalarReductionExtension l E Y n).obj M) V
          ((y.unit.app M).val.app (op V) z) := by
    simp only [adj₂, Adjunction.comp_unit_app]
    rfl
  refine ⟨e, ?_, ?_⟩
  · intro M V z
    have h := he M V z
    change (e.hom.app M).val.app (op ((proEtaleBaseChange g).obj V))
      ((adj₁.unit.app M).val.app (op V) z) = (adj₂.unit.app M).val.app (op V) z at h
    simpa only [hu₁, hu₂] using h
  · intro e' he'
    apply Iso.ext
    apply NatTrans.ext
    funext M
    apply (adj₁.homEquiv M _).injective
    rw [adj₁.homEquiv_leftAdjointUniq_hom_app adj₂]
    rw [Adjunction.homEquiv_unit]
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro V
    ext z
    change (e'.hom.app M).val.app ((proEtaleBaseChange g).op.obj V)
      ((adj₁.unit.app M).val.app V z) = (adj₂.unit.app M).val.app V z
    rw [hu₁ M V.unop, hu₂ M V.unop]
    exact he' M V.unop z

/-- The uniquely unit-normalized ordinary quotient/pullback comparison.
Source: blueprint coefficient balancing
(blueprint: def-pur-canonical-tate-comparisons). -/
def ordinaryReductionSquare {X Y : Scheme.{u}} (g : X ⟶ Y) (n : ℕ) :=
  (ordinaryReductionSquare_existsUnique l E g n).exists.choose

/-- Ordinary inverse image of a flat single root line remains K-flat.
Source: blueprint flat root representatives and exact isomorphism pullback
(blueprint: def-pur-canonical-tate-comparisons).
Proof: the normalized line pullback comparison identifies this single complex
with the good integral single line on X. Tensor that isomorphism with each acyclic
test complex. Acyclicity is preserved by the resulting isomorphism of complexes,
so integralGood proves K-flatness. -/
theorem ordinaryPulledLine_kflat {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] (r : ℕ) :
    CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      (J := ProEt.topology X) (R := completedIntegralCommRingSheafUnrestricted l E X)
      ((CochainComplex.singleFunctor _ 0).obj
        ((modulePull l E g).obj (positiveLine l E Y r))) := by
  let R := completedIntegralCommRingSheafUnrestricted l E X
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients R
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients R
  intro F hF i
  exact ((integralGood l E X r).1 F hF i).of_iso
    (((MonoidalCategory.curriedTensor _).map₂CochainComplex.obj F).mapIso
      ((CochainComplex.singleFunctor _ 0).mapIso (sfOrientationIntegralLineMaps l E g r).symm))

/-- Reduction of a flat single module, computed by the universal derived counit.
Source: Stacks 06YY, blueprint degree-zero root models
(blueprint: def-pur-canonical-tate-comparisons). -/
def reductionSingle (X : Scheme.{u}) (n : ℕ) (M : integralTowerModules l E X)
    (hM : CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      (J := ProEt.topology X) (R := completedIntegralCommRingSheafUnrestricted l E X)
      ((CochainComplex.singleFunctor _ 0).obj M)) :
    (scalarReductionDerivedExtension l E X n).obj
        ((DerivedCategory.singleFunctor _ 0).obj M) ≅
      (DerivedCategory.singleFunctor _ 0).obj ((scalarReductionExtension l E X n).obj M) :=
  reductionModel l E X n ((CochainComplex.singleFunctor _ 0).obj M) hM ≪≫
    DerivedCategory.Q.mapIso
      ((HomologicalComplex.singleMapHomologicalComplex
        (scalarReductionExtension l E X n) (.up ℤ) 0).app M)

/-- Source representative comparison for the reduction square on a Tate line.
Source: blueprint specified completed augmentation and quotient counit
(blueprint: def-pur-canonical-tate-comparisons). -/
def reductionSquareSource {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] (n r : ℕ) :
    (scalarReductionDerivedExtension l E X n).obj
        ((integralDerivedPullback l E g).obj (sfIntegralTwistingObject l E Y (r : ℤ))) ≅
      (DerivedCategory.singleFunctor _ 0).obj ((scalarReductionExtension l E X n).obj
        ((modulePull l E g).obj (positiveLine l E Y r))) :=
  (scalarReductionDerivedExtension l E X n).mapIso
      (completedToOrdinaryOnGood l E g (integralComplex l E Y r)
        (integralGood l E Y r) (sfIntegralTwistingObject_mem l E Y (r : ℤ)) ≪≫
      ((modulePull l E g).mapDerivedCategorySingleFunctor 0).app (positiveLine l E Y r)) ≪≫
    reductionSingle l E X n _ (ordinaryPulledLine_kflat l E g r)

/-- Target representative comparison for reduction on a Tate line.
Source: blueprint exact finite inverse image and universal quotient counit
(blueprint: def-pur-canonical-tate-comparisons). -/
def reductionSquareTarget {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] (n r : ℕ) :
    (finiteDerivedPullback l E n g).obj
        ((scalarReductionDerivedExtension l E Y n).obj
          (sfIntegralTwistingObject l E Y (r : ℤ))) ≅
      (DerivedCategory.singleFunctor _ 0).obj ((finiteModulePull l E g n).obj
        ((scalarReductionExtension l E Y n).obj (positiveLine l E Y r))) := by
  letI := sfIntrinsicPullback_additive (finiteCoefficientRing l E (n + 1)) g
  letI := sfIntrinsicPullback_preservesFiniteLimits (finiteCoefficientRing l E (n + 1)) g
  letI := sfIntrinsicPullback_preservesFiniteColimits (finiteCoefficientRing l E (n + 1)) g
  exact (finiteDerivedPullback l E n g).mapIso
      (reductionSingle l E Y n _ (integralGood l E Y r).1) ≪≫
    ((Functor.mapDerivedCategoryNatIso (finiteRealization l E g n)).app _).symm ≪≫
    ((finiteModulePull l E g n).mapDerivedCategorySingleFunctor 0).app _

/-- The canonical integral-to-finite pullback square on a root line, conjugating
the double-unit-normalized ordinary comparison by its specified representative maps.
Source: blueprint coefficient balancing on flat Tate representatives
(blueprint: def-pur-canonical-tate-comparisons). -/
def reductionSquare {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] (n r : ℕ) :
    (scalarReductionDerivedExtension l E X n).obj
        ((integralDerivedPullback l E g).obj (sfIntegralTwistingObject l E Y (r : ℤ))) ≅
      (finiteDerivedPullback l E n g).obj
        ((scalarReductionDerivedExtension l E Y n).obj
          (sfIntegralTwistingObject l E Y (r : ℤ))) :=
  reductionSquareSource l E g n r ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso
      ((ordinaryReductionSquare l E g n).app (positiveLine l E Y r)) ≪≫
    (reductionSquareTarget l E g n r).symm

/-- Integral-to-finite reduction restricted to the specified constructible domain.
Source: blueprint derived coefficient functors
(blueprint: def-pur-canonical-tate-comparisons). -/
def constructibleReduction (X : Scheme.{u}) (n : ℕ) :=
  (sfIntegralConstructible l E X).ι ⋙ scalarReductionDerivedExtension l E X n

end WeilConjectures.CanonicalTate
