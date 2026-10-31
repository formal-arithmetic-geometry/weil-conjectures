/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RationalSmoothPurityCanonical
public import WeilConjectures.AlgebraicGeometry.FieldShriekCompositionQcqs
public import WeilConjectures.AlgebraicGeometry.FieldWeilShriekShiftData
public import WeilConjectures.SixFunctors.IntegralOperationShiftData
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctorialitySupplement
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.Data.Nat.Prime.Infinite
import WeilConjectures.AlgebraicGeometry.CanonicalTateComparisons
import all WeilConjectures.Algebra.Homology.FlatSingleDerivedNormalization
import WeilConjectures.AlgebraicGeometry.PositiveRootTensorProduct
import WeilConjectures.AlgebraicGeometry.IntegralResidueTor
import WeilConjectures.AlgebraicGeometry.IntrinsicCoefficientTwistsUnrestricted

/-! # Rational purity: LineComparisons

Source: current blueprint, rational purity trace and coherence construction.
Existing declarations are retained in this compilation subdivision.
(blueprint: def-pur-rational-purity-line-comparisons).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
universe u v
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
open WeilConjectures

attribute [-instance] integralOperationsSiteSmall
  integralReductionSiteEssentiallySmall
attribute [local irreducible] IntegralOnSlice.completion IntegralOnSlice.completionComparison
  IntegralOnSlice.completionUnit IntegralOnSlice.roosUnit IntegralAmbient.tensorTowerIso
  IntegralOnSlice.tower IntegralOnSlice.augmentation
  integralOperationsTensorTowerFunctor IntegralSystemRealization.tensorShifts

attribute [local irreducible] sfIntegralConstructible finiteTorConstructibleIntegral
  completedIntegralCoefficientSheafUnrestricted
  AlgebraicGeometry.Scheme.residueField
  PurCompactSupport.image sfIntrinsicModuleEquivalence ProEtale.comparisonUpperStar
  IntegralOnSlice.duality integralDerivedPullback integralCompletedTensor
  sfRationalScalarExtension HasDerivedCategory.standard SheafOfModules.monoidalCategory
  Iso.trans Iso.prod Functor.mapDerivedCategory
  Functor.mapDerivedCategoryFactors Functor.leftAdjoint
attribute [local instance 5000] integralTowerHasDerivedCategory scalarReductionTargetDerived
attribute [local irreducible] ScalarLocalization.composition ScalarLocalization.transportHom

namespace WeilConjectures.RationalPurityCoherence
open FrobeniusCoefficientTwists RationalSmoothPurityCanonical

attribute [local irreducible] integralSource integralTraceTranspose rationalSourceComparison
  smallModelIso rationalIso commonIso

section Lines
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The cartesian root-line map at any morphism, fixed on local scalar/root tensors.
Source: proof Step 4, geometric source comparisons
(blueprint: def-pur-rational-purity-line-comparisons).
Proof: pull back the Kummer root tower, extend coefficients using the specified
coefficient map, and take tensor powers. At zero use the coefficient unit. The
root line is locally free of rank one and its root projections are cartesian,
so these maps are invertible. Local pure tensors determine the maps uniquely. -/
theorem linePull_existsUnique {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] :
    ∃! τ : ∀ d : ℕ, (modulePull l E f).obj (positiveLine l E Y d) ≅
        positiveLine l E X d,
      ∀ (d : ℕ) (V : Y.ProEt)
        (a : (completedIntegralCoefficientSheafUnrestricted l E Y).obj.obj (op V))
        (x : Fin d → (purTwistZlOne Y l).obj.obj (op V)),
        (τ d).hom.val.app (op ((proEtaleBaseChange f).obj V))
            (moduleSection l E f (positiveLine l E Y d) V
              (generator l E Y (op V) a d x)) =
          generator l E X (op ((proEtaleBaseChange f).obj V))
            ((sfCompletedCoefficientMap l E f).hom.app (op V) a)
            d (fun i ↦ rootSection l f V (x i)) := by
  exact sfOrientationIntegralLineMaps_existsUnique l E f

/-- The uniquely root-normalized nonnegative line pullback.
Source: proof Step 4 (blueprint: def-pur-rational-purity-line-comparisons). -/
@[irreducible]
def linePull {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] (d : ℕ) :=
  (linePull_existsUnique l E f).exists.choose d

section RootTensorProof
attribute [local instance 3000] completedIntegralCoefficientCommRingUnrestricted

private noncomputable abbrev sectionModule (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (T : Scheme.{u}) (U : T.ProEtᵒᵖ) (M : integralTowerModules l E T) :
    Module ((completedIntegralCommRingSheafUnrestricted l E T).obj.obj U)
      (M.val.obj U) := (M.val.obj U).isModule

attribute [local instance 3000] sectionModule

private noncomputable abbrev sectionSmul (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (T : Scheme.{u}) (U : T.ProEtᵒᵖ) (M : integralTowerModules l E T)
    (b : (completedIntegralCoefficientSheafUnrestricted l E T).obj.obj U)
    (x : M.val.obj U) : M.val.obj U :=
  @SMul.smul ((completedIntegralCommRingSheafUnrestricted l E T).obj.obj U)
    (M.val.obj U) (sectionModule l E T U M).toSMul b x

private theorem generator_mul (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (T : Scheme.{u}) (U : T.ProEtᵒᵖ)
    (a b : (completedIntegralCoefficientSheafUnrestricted l E T).obj.obj U) :
    ∀ (d : ℕ) (x : Fin d → (purTwistZlOne T l).obj.obj U),
      generator l E T U (a * b) d x =
      sectionSmul l E T U (positiveLine l E T d) b (generator l E T U a d x) := by
  intro d
  induction d using Nat.twoStepInduction with
  | zero => intro x; exact mul_comm a b
  | one =>
    intro x
    let : Module ((completedIntegralCoefficientSheafUnrestricted l E T).obj.obj U)
        ((purTwistIntegralOne T l E).val.obj U) := purTwistIntegralAction T l E U
    change (a * b) • (purTwistIntegralTensor T l E U 1 (x 0)) =
      b • (a • (purTwistIntegralTensor T l E U 1 (x 0)))
    rw [mul_comm a b, mul_smul]
  | more d _ ih =>
    intro x
    simp only [generator]
    rw [ih]
    let R : Sheaf (ProEt.topology T) CommRingCat.{u + 1} :=
      completedIntegralCommRingSheafUnrestricted l E T
    let M : integralTowerModules l E T := positiveLine l E T (d + 1)
    let N : integralTowerModules l E T := purTwistIntegralModule T l E
    let : EssentiallySmall.{u + 1} T.ProEt := essentiallySmallSelf.{0} _
    let : HasSheafify (ProEt.topology T) AddCommGrpCat.{u + 1} :=
      hasSheafifyEssentiallySmallSite _ _
    let : (ProEt.topology T).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
      GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _
    let q := (((PresheafOfModules.sheafificationAdjunction.{u + 1}
      (R := (sheafCompose (ProEt.topology T)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)
      (𝟙 _)).unit.app (SheafOfModules.siteTensorPresheaf (R := R.obj) M.val N.val)).app U).hom
    let v : M.val.obj U := generator l E T U a (d + 1) (fun i ↦ x i.castSucc)
    let w : N.val.obj U := purTwistIntegralTensor T l E U 1 (x (Fin.last (d + 1)))
    have ht := TensorProduct.smul_tmul' (R := R.obj.obj U) (R' := R.obj.obj U) b v w
    exact (congrArg q ht.symm).trans (q.map_smul b _)

private theorem pair_balance (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (T : Scheme.{u}) (U : T.ProEtᵒᵖ) (M N : integralTowerModules l E T)
    (b : (completedIntegralCoefficientSheafUnrestricted l E T).obj.obj U)
    (x : M.val.obj U) (y : N.val.obj U) :
    proEtaleTensorPair T (completedIntegralCommRingSheafUnrestricted l E T)
        M N U (sectionSmul l E T U M b x) y =
      proEtaleTensorPair T (completedIntegralCommRingSheafUnrestricted l E T)
        M N U x (sectionSmul l E T U N b y) := by
  unfold proEtaleTensorPair
  exact congrArg _ (congrArg _ (TensorProduct.smul_tmul
    (R := (completedIntegralCommRingSheafUnrestricted l E T).obj.obj U)
    (R' := (completedIntegralCommRingSheafUnrestricted l E T).obj.obj U) b x y))

/-- Concatenation of root powers, including the coefficient unit at either zero.
Source: proof Step 4, tensor and shift associators
(blueprint: def-pur-rational-purity-line-comparisons).
Proof: concatenate local pure root tensors. Balanced tensor relations make this
linear, and sheafification gives the indicated map. Reassociate and split the
ordered powers for its inverse. The two local tensor formulas are inverse;
local pure tensors generate, proving uniqueness as well as the inverse equations. -/
theorem lineAdd_existsUnique (T : Scheme.{u}) (d e : ℕ) :
    ∃! a : positiveLine l E T (d + e) ≅
        ((proEtaleOrdinaryTensor T
          (completedIntegralCommRingSheafUnrestricted l E T)).obj
            (positiveLine l E T d)).obj (positiveLine l E T e),
      ∀ (U : T.ProEtᵒᵖ)
        (b : (completedIntegralCoefficientSheafUnrestricted l E T).obj.obj U)
        (x : Fin (d + e) → (purTwistZlOne T l).obj.obj U),
        a.hom.val.app U (generator l E T U b (d + e) x) =
          proEtaleTensorPair T
            (completedIntegralCommRingSheafUnrestricted l E T)
            (positiveLine l E T d) (positiveLine l E T e) U
            (generator l E T U b d (fun i ↦ x (Fin.castAdd e i)))
            (generator l E T U 1 e (fun i ↦ x (Fin.natAdd d i))) := by
  obtain ⟨m, hm, huniq⟩ := positiveRootTensorProduct_existsUnique l E T d e
  have hsplit (U : T.ProEtᵒᵖ)
      (a : (completedIntegralCoefficientSheafUnrestricted l E T).obj.obj U)
      (x : Fin (d + e) → (purTwistZlOne T l).obj.obj U) :
      m.hom.val.app U (proEtaleTensorPair T
        (completedIntegralCommRingSheafUnrestricted l E T)
        (positiveLine l E T d) (positiveLine l E T e) U
        (generator l E T U a d (fun i ↦ x (Fin.castAdd e i)))
        (generator l E T U 1 e (fun i ↦ x (Fin.natAdd d i)))) =
      generator l E T U a (d + e) x := by
    have hx : Fin.addCases (fun i ↦ x (Fin.castAdd e i))
        (fun i ↦ x (Fin.natAdd d i)) = x := by
      funext i
      exact Fin.addCases (fun j ↦ by simp) (fun j ↦ by simp) i
    simpa only [mul_one, hx, proEtaleTensorPair,
      SheafOfModules.ScalarHomOrdinary.pure] using hm U a 1
      (fun i ↦ x (Fin.castAdd e i)) (fun i ↦ x (Fin.natAdd d i))
  refine ⟨m.symm, ?_, ?_⟩
  · intro U a x
    rw [← hsplit U a x]
    exact ModuleCat.inv_hom_apply ((SheafOfModules.evaluation _ U).mapIso m) _
  · intro other hother
    have hinv : ∀ (U : T.ProEtᵒᵖ)
        (a b : (completedIntegralCoefficientSheafUnrestricted l E T).obj.obj U)
        (x : Fin d → (purTwistZlOne T l).obj.obj U)
        (y : Fin e → (purTwistZlOne T l).obj.obj U),
        other.inv.val.app U (SheafOfModules.ScalarHomOrdinary.pure
          (completedIntegralCommRingSheafUnrestricted l E T) _ _ U
          (generator l E T U a d x) (generator l E T U b e y)) =
        generator l E T U (a * b) (d + e) (Fin.addCases x y) := by
      intro U a b x y
      have h := hother U (a * b) (Fin.addCases x y)
      simp only [Fin.addCases_left, Fin.addCases_right] at h
      rw [generator_mul l E T U a b d x, pair_balance,
        ← generator_mul l E T U 1 b e y, one_mul] at h
      change other.inv.val.app U (proEtaleTensorPair T _ _ _ U _ _) = _
      rw [← h]
      exact ModuleCat.inv_hom_apply ((SheafOfModules.evaluation _ U).mapIso other) _
    have h := congrArg Iso.symm (huniq other.symm hinv)
    simpa only [Iso.symm_symm_eq] using h

end RootTensorProof

attribute [local irreducible] Functor.mapIso ordinaryModel

/-- The actual concatenation map, selected from its uniquely determining formula.
Source: proof Step 4 (blueprint: def-pur-rational-purity-line-comparisons). -/
@[irreducible]
def lineAdd (T : Scheme.{u}) (d e : ℕ) :=
  (lineAdd_existsUnique l E T d e).exists.choose

/-- Rank-one root lines are flat-term K-flat representatives.
Source: proof Step 1, uniform finite-Tor domain
(blueprint: def-pur-rational-purity-line-comparisons).
Proof: trivialize the root line on a pro-etale cover. Each power is the coefficient
unit there, hence flat. A degree-zero flat complex is K-flat; these are exactly
the two clauses of integralOperationsGoodComplex. -/
theorem lineSingle_good (T : Scheme.{u})
    [∀ x : T, Invertible (l : T.residueField x)] (d : ℕ) :
    integralOperationsGoodComplex l E T
      ((CochainComplex.singleFunctor _ 0).obj (positiveLine l E T d)) := by
  let R := completedIntegralCommRingSheafUnrestricted l E T
  have hline := (@coefficientTwistLine_exact T R (purTwistIntegralModule T l E)
    ((pur_twist_sheaf_locally_free.{u, 0} T l E).2.2.1.2.2.1) (d : ℤ)).2
  exact ⟨SheafOfModules.FlatSingleDerivedNormalization.single_kFlat R
    (positiveLine l E T d) hline,
    SheafOfModules.FlatSingleDerivedNormalization.single_flat_terms R
      (positiveLine l E T d) hline⟩

/-- The same complete line has uniform finite-Tor amplitude [0,0].
Source: proof Step 1 (blueprint: def-pur-rational-purity-line-comparisons).
Proof: the compatible Kummer tower recovers the complete line. Every quotient
is locally a free rank-one coefficient module, in degree zero; therefore the
constructibility, completeness and uniform finite-Tor clauses all hold. -/
theorem lineSingle_finiteTor (T : Scheme.{u})
    [∀ x : T, Invertible (l : T.residueField x)] (d : ℕ) :
    finiteTorConstructibleIntegral l E T
      (DerivedCategory.Q.obj
        ((CochainComplex.singleFunctor _ 0).obj (positiveLine l E T d))) := by
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
  rw [← (integral_residue_tor D l hl E T).2]
  exact (sfIntegralConstructible l E T).prop_of_iso
    ((DerivedCategory.singleFunctorIsoCompQ _ 0).app (positiveLine l E T d))
    (sfIntegralTwistingObject_mem l E T (d : ℤ))

/-- Pullback of a complete rank-one root line has the specified complete augmentation.
Source: proof Step 4, arbitrary geometric base change
(blueprint: def-pur-rational-purity-line-comparisons).
Proof: linePull identifies ordinary inverse image with the target complete line.
Under that identification the strict quotient augmentation is the completeness
unit, whose product projections and second cone component are prescribed. Thus
its localization is invertible, for arbitrary f, without smoothness of f. -/
theorem linePullAugmentation_isIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] (d : ℕ) :
    IsIso (DerivedCategory.Q.map ((pullbackAugmentation l E f).app
      ((CochainComplex.singleFunctor _ 0).obj (positiveLine l E Y d)))) := by
  exact CanonicalTate.integralPullUnit_isIso l E f d

/-- Integral line pullback from the fixed strict augmentation and local root map.
Source: proof Step 4 (blueprint: def-pur-rational-purity-line-comparisons). -/
@[irreducible]
def integralLinePull {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] (d : ℕ) :
    (integralDerivedPullback l E f).obj (sfIntegralTwistingObject l E Y (d : ℤ)) ≅
      sfIntegralTwistingObject l E X (d : ℤ) :=
  (integralDerivedPullback l E f).mapIso
      ((DerivedCategory.singleFunctorIsoCompQ _ 0).app (positiveLine l E Y d)) ≪≫
    (integralDerivedPullbackComparison l E f).app
      ⟨_, lineSingle_good l E Y d⟩ ≪≫
    (@asIso _ _ _ _ (DerivedCategory.Q.map ((pullbackAugmentation l E f).app
      ((CochainComplex.singleFunctor _ 0).obj (positiveLine l E Y d))))
        (linePullAugmentation_isIso l E f d)).symm ≪≫
    ((modulePull l E f).mapDerivedCategoryFactors.app _).symm ≪≫
    ((modulePull l E f).mapDerivedCategorySingleFunctor 0).app (positiveLine l E Y d) ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso (linePull l E f d)

/-- Rationalization of the specified integral line pullback.
Source: proof Steps 2 and 4 (blueprint: def-pur-rational-purity-line-comparisons). -/
@[irreducible]
def rationalLinePull {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] (d : ℕ) :
    (rationalDerivedPullback l E f).obj (sfRationalTwistingCoefficient l E Y (d : ℤ)) ≅
      sfRationalTwistingCoefficient l E X (d : ℤ) :=
  eqToIso ((rationalDerivedPullback_existsUnique l E f).exists.choose_spec.2.1 _) ≪≫
    (sfRationalConstructibleLocalization l E X).mapIso
      (ObjectProperty.isoMk _ (integralLinePull l E f d))

attribute [local irreducible] rationalDerivedPullback

/-- The total tensor of degree-zero lines is the degree-zero ordinary tensor.
Source: proof Step 4 (blueprint: def-pur-rational-purity-line-comparisons). -/
@[irreducible]
def lineSingleTensor (T : Scheme.{u}) (d e : ℕ) :
    (ordinaryTotal l E T).obj
      ((CochainComplex.singleFunctor _ 0).obj (positiveLine l E T d),
        (CochainComplex.singleFunctor _ 0).obj (positiveLine l E T e)) ≅
      (CochainComplex.singleFunctor _ 0).obj
        (((proEtaleOrdinaryTensor T
          (completedIntegralCommRingSheafUnrestricted l E T)).obj
            (positiveLine l E T d)).obj (positiveLine l E T e)) :=
  (CochainComplex.map₂HomologicalComplexFlipObjSingleIso
    (proEtaleOrdinaryTensor T (completedIntegralCommRingSheafUnrestricted l E T))
      (positiveLine l E T e)).app
        ((CochainComplex.singleFunctor _ 0).obj (positiveLine l E T d)) ≪≫
    (HomologicalComplex.singleMapHomologicalComplex
      ((proEtaleOrdinaryTensor T
        (completedIntegralCommRingSheafUnrestricted l E T)).flip.obj (positiveLine l E T e))
        (.up ℤ) 0).app (positiveLine l E T d)

attribute [local irreducible] coefficientTotalTensor

/-- Concatenation in the completed derived tensor, through the fixed strict tensor unit.
Source: proof Step 4 (blueprint: def-pur-rational-purity-line-comparisons). -/
@[irreducible]
def integralLineAdd (T : Scheme.{u})
    [∀ x : T, Invertible (l : T.residueField x)] (d e : ℕ) :
    sfIntegralTwistingObject l E T ((d + e : ℕ) : ℤ) ≅
      (integralCompletedTensor l E T).obj
        (sfIntegralTwistingObject l E T (d : ℤ), sfIntegralTwistingObject l E T (e : ℤ)) :=
  (DerivedCategory.singleFunctor _ 0).mapIso (lineAdd l E T d e) ≪≫
    (DerivedCategory.singleFunctorIsoCompQ _ 0).app _ ≪≫
    DerivedCategory.Q.mapIso (lineSingleTensor l E T d e).symm ≪≫
    (@asIso _ _ _ _ (DerivedCategory.Q.map ((tensorAugmentation l E T).app
      ((CochainComplex.singleFunctor _ 0).obj (positiveLine l E T d),
        (CochainComplex.singleFunctor _ 0).obj (positiveLine l E T e))))
      (tensorAugmentation_isIso l E T _ _ (lineSingle_good l E T d)
        (lineSingle_good l E T e) (lineSingle_finiteTor l E T d)
        (lineSingle_finiteTor l E T e))) ≪≫
    ((integralCompletedTensorComparison l E T).app
      (⟨_, lineSingle_good l E T d⟩, ⟨_, lineSingle_good l E T e⟩)).symm ≪≫
    (integralCompletedTensor l E T).mapIso
      (Iso.prod ((DerivedCategory.singleFunctorIsoCompQ _ 0).app _).symm
        ((DerivedCategory.singleFunctorIsoCompQ _ 0).app _).symm)

/-- The standard arithmetic equality for the two even shifts.
Source: proof Step 4 (blueprint: def-pur-rational-purity-line-comparisons).
Proof: cast addition from natural numbers to integers and distribute multiplication. -/
theorem evenShift_add (d e : ℕ) :
    2 * ((d + e : ℕ) : ℤ) = 2 * (d : ℤ) + 2 * (e : ℤ) := by
  simp only [Nat.cast_add, mul_add]

/-- Reassociate the two completed tensor shifts, retaining their signed Roos maps.
Source: proof Step 4 (blueprint: def-pur-rational-purity-line-comparisons). -/
@[irreducible]
def integralTensorBothShift (T : Scheme.{u})
    (M N : DerivedCategory (integralTowerModules l E T)) (r s : ℤ) :
    (integralCompletedTensor l E T).obj (M⟦r⟧, N⟦s⟧) ≅
      ((integralCompletedTensor l E T).obj (M,N))⟦r + s⟧ :=
  ((IntegralSystemRealization.tensorShifts l E).integralLeft T r).app (M,N⟦s⟧) ≪≫
    (shiftFunctor _ r).mapIso
      (((IntegralSystemRealization.tensorShifts l E).integralRight T s).app (M,N)) ≪≫
    (shiftFunctorAdd' _ s r (r + s) (Int.add_comm s r)).symm.app _

/-- The shifted integral line concatenation in the actual intrinsic category.
Source: proof Step 4 (blueprint: def-pur-rational-purity-line-comparisons). -/
@[irreducible]
def integralShiftedLineAdd (T : Scheme.{u})
    [∀ x : T, Invertible (l : T.residueField x)] (d e : ℕ) :
    (sfIntegralTwistingCoefficient l E T ((d + e : ℕ) : ℤ))⟦2*((d+e : ℕ) : ℤ)⟧ ≅
      (constructibleIntegralTensor l E T).obj
        ((sfIntegralTwistingCoefficient l E T (d : ℤ))⟦2*(d : ℤ)⟧,
          (sfIntegralTwistingCoefficient l E T (e : ℤ))⟦2*(e : ℤ)⟧) :=
  (sfIntegralConstructible l E T).isoMk
    ((((sfIntegralConstructible l E T).ι.commShiftIso (2*((d+e : ℕ) : ℤ))).app _) ≪≫
      (shiftFunctor _ (2*((d+e : ℕ) : ℤ))).mapIso (integralLineAdd l E T d e) ≪≫
      (eqToIso (congrArg (fun n : ℤ ↦
        ((integralCompletedTensor l E T).obj
          (sfIntegralTwistingObject l E T (d : ℤ),
            sfIntegralTwistingObject l E T (e : ℤ)))⟦n⟧)
              (evenShift_add d e))) ≪≫
      (integralTensorBothShift l E T _ _ (2*(d : ℤ)) (2*(e : ℤ))).symm ≪≫
      (integralCompletedTensor l E T).mapIso
        (Iso.prod (((sfIntegralConstructible l E T).ι.commShiftIso (2*(d : ℤ))).app
          (sfIntegralTwistingCoefficient l E T (d : ℤ))).symm
          (((sfIntegralConstructible l E T).ι.commShiftIso (2*(e : ℤ))).app
            (sfIntegralTwistingCoefficient l E T (e : ℤ))).symm))

/-- Even-shifted line concatenation after actual scalar localization.
Source: proof Steps 2 and 4 (blueprint: def-pur-rational-purity-line-comparisons). -/
@[irreducible]
def rationalShiftedLineAdd (T : Scheme.{u})
    [∀ x : T, Invertible (l : T.residueField x)] (d e : ℕ) :
    (sfRationalTwistingCoefficient l E T ((d + e : ℕ) : ℤ))⟦2*((d+e : ℕ) : ℤ)⟧ ≅
      (rationalDerivedTensor l E T).obj
        ((sfRationalTwistingCoefficient l E T (d : ℤ))⟦2*(d : ℤ)⟧,
          (sfRationalTwistingCoefficient l E T (e : ℤ))⟦2*(e : ℤ)⟧) :=
  ((sfRationalConstructibleLocalization l E T).commShiftIso
      (2*((d+e : ℕ) : ℤ))).symm.app _ ≪≫
    (sfRationalConstructibleLocalization l E T).mapIso (integralShiftedLineAdd l E T d e) ≪≫
    (eqToIso ((rationalDerivedTensor_existsUnique l E T).exists.choose_spec.1
      ((sfRationalConstructibleLocalization l E T).obj
          ((sfIntegralTwistingCoefficient l E T (d : ℤ))⟦2*(d : ℤ)⟧),
        (sfRationalConstructibleLocalization l E T).obj
          ((sfIntegralTwistingCoefficient l E T (e : ℤ))⟦2*(e : ℤ)⟧)))).symm ≪≫
    (rationalDerivedTensor l E T).mapIso
      (Iso.prod (((sfRationalConstructibleLocalization l E T).commShiftIso
        (2*(d : ℤ))).app _) (((sfRationalConstructibleLocalization l E T).commShiftIso
          (2*(e : ℤ))).app _))

attribute [local irreducible] rationalDerivedTensor

/-- Pullback of the shifted line, using the normalized pullback shift comparison.
Source: proof Step 4 (blueprint: def-pur-rational-purity-line-comparisons). -/
@[irreducible]
def rationalShiftedLinePull {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] (d : ℕ) :
    (rationalDerivedPullback l E f).obj
        ((sfRationalTwistingCoefficient l E Y (d : ℤ))⟦2*(d : ℤ)⟧) ≅
      (sfRationalTwistingCoefficient l E X (d : ℤ))⟦2*(d : ℤ)⟧ :=
  ((rationalDerivedPullback l E f).commShiftIso (2*(d : ℤ))).app _ ≪≫
    (shiftFunctor _ (2*(d : ℤ))).mapIso (rationalLinePull l E f d)

/-- The geometric source compositor, assembled from root concatenation, tensor
associativity, pullback composition and the normalized cartesian line comparison.
Source: proof Step 4 (blueprint: def-pur-rational-purity-line-comparisons). -/
@[irreducible]
def rationalSourceComposition {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    [∀ z : Z, Invertible (l : Z.residueField z)] (d e : ℕ)
    (K : sfRationalConstructibleCategory l E Z) :
    (rationalSource l E (f ≫ g) (d + e)).obj K ≅
      (rationalSource l E f d).obj ((rationalSource l E g e).obj K) :=
  (rationalDerivedTensor l E X).mapIso
      (Iso.prod (rationalShiftedLineAdd l E X d e)
        ((fieldRationalPullComp l E f g).app K)) ≪≫
    pullbackTensorRationalAssociator l E X _ _ _ ≪≫
    (rationalDerivedTensor l E X).mapIso
      (Iso.prod (Iso.refl _)
        ((rationalDerivedTensor l E X).mapIso
          (Iso.prod (rationalShiftedLinePull l E f e).symm (Iso.refl _)) ≪≫
          (canonicalRationalPullbackTensor l E f
            ((sfRationalTwistingCoefficient l E Y (e : ℤ))⟦2*(e : ℤ)⟧)
              ((rationalDerivedPullback l E g).obj K)).symm))

/-- Pullback around the given Cartesian square, from the two actual compositors.
Source: proof Step 4 (blueprint: def-pur-rational-purity-line-comparisons). -/
@[irreducible]
def rationalSquarePull {X' X Y' Y : Scheme.{u}}
    (a : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (b : Y' ⟶ Y)
    [∀ x : X', Invertible (l : X'.residueField x)]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y', Invertible (l : Y'.residueField y)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (sq : IsPullback a f' f b) :
    rationalDerivedPullback l E f ⋙ rationalDerivedPullback l E a ≅
      rationalDerivedPullback l E b ⋙ rationalDerivedPullback l E f' :=
  (fieldRationalPullComp l E a f).symm ≪≫
    eqToIso (congrArg (fun h : X' ⟶ Y ↦ rationalDerivedPullback l E h) sq.w) ≪≫
    fieldRationalPullComp l E f' b

/-- The source base-change isomorphism for any Cartesian square. It uses no purity
map and imposes no smoothness on the horizontal base-change morphism.
Source: proof Step 4 (blueprint: def-pur-rational-purity-line-comparisons). -/
@[irreducible]
def rationalSourceBaseChange {X' X Y' Y : Scheme.{u}}
    (a : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (b : Y' ⟶ Y)
    [∀ x : X', Invertible (l : X'.residueField x)]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y', Invertible (l : Y'.residueField y)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (sq : IsPullback a f' f b) (d : ℕ)
    (K : sfRationalConstructibleCategory l E Y) :
    (rationalDerivedPullback l E a).obj ((rationalSource l E f d).obj K) ≅
      (rationalSource l E f' d).obj ((rationalDerivedPullback l E b).obj K) :=
  canonicalRationalPullbackTensor l E a _ _ ≪≫
    (rationalDerivedTensor l E X').mapIso
      (Iso.prod (rationalShiftedLinePull l E a d)
        ((rationalSquarePull l E a f' f b sq).app K))

end Lines

end WeilConjectures.RationalPurityCoherence
