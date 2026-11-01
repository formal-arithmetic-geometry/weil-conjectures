/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.Pod.PodCompletionReindexShifts
public import WeilConjectures.PoincareDuality.Pod.PodNativeRoosFunctorComparison
public import WeilConjectures.CategoryTheory.RoosConeCalculus.RoosConeCalculus
import all WeilConjectures.PoincareDuality.Pod.PodCompletionReindexShifts
import all WeilConjectures.PoincareDuality.Pod.PodNativeRoosFunctorComparison
import all WeilConjectures.CategoryTheory.RoosConeCalculus.RoosConeCalculus
import all WeilConjectures.SmoothPurity.SequenceKInjectiveComparison.SequenceKInjectiveComparisonShifts
import all WeilConjectures.CategoryTheory.Strict.StrictRoosShiftLocalization
public import Mathlib.CategoryTheory.Limits.HasLimits
public import WeilConjectures.Mathlib.CategoryTheory.Shift.CommShift
public import WeilConjectures.PoincareDuality.Pod.PodStrictRoosReindexShift
public import WeilConjectures.PoincareDuality.Pod.Reindexing.PodReindexingSignedRoosShift
import WeilConjectures.PoincareDuality.Pod.PodNormalizedRoosComparisonShift

/-! # K-injective normalized Roos comparison shift -/
@[expose] public noncomputable section
set_option autoImplicit false

set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local instance 5000] WeilConjectures.integralTowerHasDerivedCategory
attribute [local instance 5000] WeilConjectures.coefficientSequenceHasDerived
attribute [local instance 5000] WeilConjectures.coefficientFiniteHasDerived
attribute [local instance 5000] WeilConjectures.integralOperationsCommHasDerivedCategory
attribute [local irreducible] HasDerivedCategory.standard
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite AlgebraicGeometry
namespace WeilConjectures
attribute [local instance 50000] WeilConjectures.podSheafCanonicalPreadditive

universe a b t u

-- Keep the coefficient universe explicit during sheafification synthesis.
private instance (priority := 20000) fixedAbSheafify (Z : Scheme.{u}) :
    HasSheafify (AlgebraicGeometry.Scheme.ProEt.topology Z) AddCommGrpCat.{u + 1} :=
  integralCoefficientAbSheafify.{u, u} Z

private instance (priority := 20000) fixedAbBijective (Z : Scheme.{u}) :
    (AlgebraicGeometry.Scheme.ProEt.topology Z).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  integralCoefficientAbLocallyBijective.{u, u} Z

/-- Translate the strict five-factor square to the native coherent Roos shift.
Source: Stacks 011G and 0941, signed Roos shift and exact relabelling
(blueprint: lem-pod-reindexing-strict-native-shift-s8).
Proof: coordinate uniqueness identifies the supplied source and target shifts with
the native shift. Expand the composite shift comparisons, use the explicit equality
of the two Roos map presentations, and apply the strict signed reindexing square. -/
private theorem podReindexingStrictNativeShift
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (D : PodCompletionReindex l E g)
    (hnat : PodCompletionReindex.RoosNaturality l E g D)
    (hshift : PodCompletionReindex.RoosShift l E g D)
    (hgen : PodCompletionReindex.RestrictedGenerators l E g D)
    (hSY : D.shiftSource.Laws) (hSX : D.shiftTarget.Laws) :
    let := CategoryTheory.RoosConeCalculus.roosCommShift
      (A := scalarReductionSource l E Y)
    let := CategoryTheory.RoosConeCalculus.roosCommShift
      (A := scalarReductionSource l E X)
    let RY := (coefficientSequenceRestriction l E Y).mapHomologicalComplex (.up ℤ)
    let RX := (coefficientSequenceRestriction l E X).mapHomologicalComplex (.up ℤ)
    let P := (integralComparisonSequencePullback l E g).mapHomologicalComplex (.up ℤ)
    let F := isoReductionIntegralComplex l E g
    let HY := RY ⋙ roosF
    let HX := RX ⋙ roosF
    let U := HY ⋙ F
    let V := P ⋙ HX
    let f (C : CochainComplex (coefficientSequenceModules l E Y) ℤ) :
      U.obj C ⟶ V.obj C := (D.roos (podRestrictedTower l E C)).hom ≫
        integralOperationsRoosFunctor.map (D.restricted C).hom
    ∀ (C : CochainComplex (coefficientSequenceModules l E Y) ℤ) (r : ℤ),
      (U.commShiftIso r).hom.app C ≫ (f C)⟦r⟧' =
      f (C⟦r⟧) ≫ (V.commShiftIso r).hom.app C := by
  dsimp only
  let := CategoryTheory.RoosConeCalculus.roosCommShift
    (A := scalarReductionSource l E Y)
  let := CategoryTheory.RoosConeCalculus.roosCommShift
    (A := scalarReductionSource l E X)
  let RY := (coefficientSequenceRestriction l E Y).mapHomologicalComplex (.up ℤ)
  let RX := (coefficientSequenceRestriction l E X).mapHomologicalComplex (.up ℤ)
  let P := (integralComparisonSequencePullback l E g).mapHomologicalComplex (.up ℤ)
  let F := isoReductionIntegralComplex l E g
  let HY := RY ⋙ roosF
  let HX := RX ⋙ roosF
  let U := HY ⋙ F
  let V := P ⋙ HX
  let f (C : CochainComplex (coefficientSequenceModules l E Y) ℤ) :
      U.obj C ⟶ V.obj C := (D.roos (podRestrictedTower l E C)).hom ≫
        integralOperationsRoosFunctor.map (D.restricted C).hom
  have hy (C : CochainComplex (coefficientSequenceModules l E Y) ℤ) (r : ℤ) :
      (Functor.commShiftIso roosF r).hom.app (RY.obj C) =
        (D.shiftSource.comparison (podRestrictedTower l E C) r).hom := by
    exact roosShift_hom_ext_complex_sheaf _ D.shiftSource hSY (RY.obj C) r
  have hx (C : CochainComplex (coefficientSequenceModules l E X) ℤ) (r : ℤ) :
      (Functor.commShiftIso roosF r).hom.app (RX.obj C) =
        (D.shiftTarget.comparison (podRestrictedTower l E C) r).hom := by
    exact roosShift_hom_ext_complex_sheaf _ D.shiftTarget hSX (RX.obj C) r
  intro C r
  simp only [Functor.commShiftIso_comp_hom_app, Functor.comp_map,
    nativeRoos_map, Category.assoc]
  erw [hy C r, hx (P.obj C) r]
  erw [F.map_comp]
  convert podStrictRoosReindexShift l E g D hnat hshift hgen hSX C r using 1
  dsimp only [podRestrictionShift, Functor.mapIso_hom, RY, RX, P, F, f,
    Functor.comp_map]
  simp only [Category.assoc]
  rfl

variable {A : Type a} [Category.{b} A] [Abelian A] [HasCountableProducts A]
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{u})
/-- The canonical derived limit shift, in the constant-tower notation.
Source: Stacks 011G and 0941
(blueprint: lem-pod-normalized-roos-comparison-shift-s8). -/
instance podNormalizedConstantLimitShift :
    (coefficientConstantTowerLimit l E W).CommShift ℤ := by
  dsimp only [coefficientConstantTowerLimit]
  infer_instance

private theorem shift_of_kinjective
    {B D : Type*} [Category B] [Category D] [Abelian B]
    [HasShift D ℤ] [Abelian.HasKInjectiveResolutions B]
    (F G : CochainComplex B ℤ ⥤ D) [F.CommShift ℤ] [G.CommShift ℤ]
    (e : F ≅ G)
    (hF : ∀ {C I : CochainComplex B ℤ} (q : C ⟶ I) [QuasiIso q], IsIso (F.map q))
    (hI : ∀ (I : CochainComplex B ℤ) [I.IsKInjective] (r : ℤ),
      (F.commShiftIso r).hom.app I ≫ (e.hom.app I)⟦r⟧' =
        e.hom.app (I⟦r⟧) ≫ (G.commShiftIso r).hom.app I) :
    NatTrans.CommShift e.hom ℤ := by
  constructor
  intro r
  ext C
  obtain ⟨I, hI', q, _, hq⟩ := Abelian.HasKInjectiveResolutions.exists_isKInjective C
  have := hF q
  have hG : G.map q = e.inv.app C ≫ F.map q ≫ e.hom.app I := by
    rw [e.hom.naturality, Iso.inv_hom_id_app_assoc]
  have : IsIso (G.map q) := hG ▸ inferInstance
  apply (cancel_mono ((G.map q)⟦r⟧')).mp
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
  change ((F.commShiftIso r).hom.app C ≫ (e.hom.app C)⟦r⟧') ≫ (G.map q)⟦r⟧' =
    (e.hom.app (C⟦r⟧) ≫ (G.commShiftIso r).hom.app C) ≫ (G.map q)⟦r⟧'
  rw [Category.assoc, ← CategoryTheory.Functor.map_comp, ← e.hom.naturality,
    CategoryTheory.Functor.map_comp]
  rw [← Category.assoc, ← F.commShiftIso_hom_naturality, Category.assoc, hI I r]
  rw [← Category.assoc, e.hom.naturality]
  simp only [Category.assoc, G.commShiftIso_hom_naturality]

private theorem shift_via_kinjective_unit
    {B D : Type*} [Category B] [Category D] [Abelian B]
    [HasShift D ℤ] [Abelian.HasKInjectiveResolutions B]
    (H F G : CochainComplex B ℤ ⥤ D)
    [H.CommShift ℤ] [F.CommShift ℤ] [G.CommShift ℤ]
    (e : F ≅ G) (η : H ⟶ F) [NatTrans.CommShift η ℤ]
    (hF : ∀ {C I : CochainComplex B ℤ} (q : C ⟶ I) [QuasiIso q], IsIso (F.map q))
    (hη : ∀ (I : CochainComplex B ℤ) [I.IsKInjective], IsIso (η.app I))
    (a : ∀ I, H.obj I ⟶ G.obj I)
    (he : ∀ (I : CochainComplex B ℤ) [I.IsKInjective], η.app I ≫ e.hom.app I = a I)
    (ha : ∀ (I : CochainComplex B ℤ) [I.IsKInjective] (r : ℤ),
      (H.commShiftIso r).hom.app I ≫ (a I)⟦r⟧' =
        a (I⟦r⟧) ≫ (G.commShiftIso r).hom.app I) :
    NatTrans.CommShift e.hom ℤ := by
  apply shift_of_kinjective F G e hF
  intro I hI r
  have := hη (I⟦r⟧)
  apply (cancel_epi (η.app (I⟦r⟧))).mp
  have hηI := NatTrans.shift_app_comm η r I
  rw [← Category.assoc, ← hηI]
  simp only [Category.assoc, ← CategoryTheory.Functor.map_comp, he]
  rw [← Category.assoc, he, ha]

private theorem limitToRoos_eq_augmentation
    (I : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ) :
    integralComparisonLimitToRoos l E W I =
      CategoryTheory.RoosConeCalculus.augmentation
        (CategoryTheory.StrictRoosShiftProof.limitModelCone I) := by
  apply (integralComparisonLimitToRoos_existsUnique l E W I).unique
    (integralComparisonLimitToRoos_existsUnique l E W I).exists.choose_spec
  constructor
  · intro n
    apply HomologicalComplex.hom_ext
    intro i
    exact CategoryTheory.RoosConeCalculus.augment_v_π
      (CategoryTheory.StrictRoosShiftProof.limitModelCone I) i n
  · intro i j h
    exact CategoryTheory.RoosConeCalculus.augment_u
      (CategoryTheory.StrictRoosShiftProof.limitModelCone I) i j (by omega)

private theorem limitToRoos_shift
    (cs : (roosF (A := scalarReductionSource l E W)).CommShift ℤ)
    (hcs : CategoryTheory.RoosConeCalculus.ShiftAugmentation cs)
    (I : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ) (r : ℤ) :
    integralComparisonLimitToRoos l E W (I⟦r⟧) ≫
      (Functor.commShiftIso roosF
        (self := cs) r).hom.app I =
    (((lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤ scalarReductionSource l E W)
      |>.mapHomologicalComplex (.up ℤ)).commShiftIso r).hom.app I ≫
      (integralComparisonLimitToRoos l E W I)⟦r⟧' := by
  rw [limitToRoos_eq_augmentation, limitToRoos_eq_augmentation]
  apply hcs
  intro q n
  simp only [CategoryTheory.StrictRoosShiftProof.limitModelCone,
    Functor.mapHomologicalComplex_commShiftIso_hom_app_f,
    CochainComplex.shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq_rfl,
    Iso.refl_hom, NatTrans.id_app]
  rfl

private theorem derivedUnit_iso
    (I : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ) [I.IsKInjective] :
    (SequenceKInjectiveComparison.derivedUnit
      (lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤ scalarReductionSource l E W)).app I =
      ((lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤ scalarReductionSource l E W)
        |>.rightDerivedFunctorObjQIso I).inv := by
  rw [SequenceKInjectiveComparison.derivedUnit_app]
  dsimp only [coefficientRightDerivedComparison, Functor.rightDerivedFunctorObjQIso,
    Iso.trans, Iso.symm, Functor.mapIso, asIso, Iso.app]
  exact (Category.assoc _ _ _).symm

/-- The K-injective-normalized comparison commutes with the integer shift.
Source: Stacks 0941 and 011G.
(blueprint: lem-pod-normalized-roos-comparison-shift-s8).
Proof: on a K-injective tower I, the canonical derived unit is the inverse
of its right-derived comparison. The prescribed normalization of ρ therefore
gives η(I) ≫ ρ(I) = Q(augmentation I). The augmentation is the limit tuple
in the first Roos coordinate and zero in the second. The hypothesis on cs
says that these augmentations commute with shifts; the canonical derived unit
also commutes with shifts. Cancel its invertible value on shifted K-injectives
to obtain the comparison shift equation there. For any complex choose a
K-injective quasi-isomorphism. Both functors invert it, so naturality and
cancellation transport that equation to the original complex. -/
theorem podNormalizedRoosComparisonCommShift
    (ρ : IntegralComparisonRoosModel l E W)
    (cs : (roosF (A := scalarReductionSource l E W)).CommShift ℤ)
    (hcs : CategoryTheory.RoosConeCalculus.ShiftAugmentation cs) :
    let := cs
    NatTrans.CommShift (ρ.comparison ≪≫
      Functor.isoWhiskerRight (podNativeRoosIso (A := scalarReductionSource l E W))
        DerivedCategory.Q).hom ℤ := by
  let := cs
  let F₀ := (lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤ scalarReductionSource l E W)
  let e : DerivedCategory.Q ⋙ F₀.rightDerivedFunctor ≅ roosF ⋙ DerivedCategory.Q :=
    ρ.comparison ≪≫ Functor.isoWhiskerRight podNativeRoosIso DerivedCategory.Q
  let η := SequenceKInjectiveComparison.derivedUnit F₀
  have : NatTrans.CommShift η ℤ :=
    SequenceKInjectiveComparison.derivedUnit_commShift F₀
  refine shift_via_kinjective_unit
    (F₀.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (DerivedCategory.Q ⋙ F₀.rightDerivedFunctor) (roosF ⋙ DerivedCategory.Q) e η
    ?_ ?_ (fun I ↦ DerivedCategory.Q.map (integralComparisonLimitToRoos l E W I)) ?_ ?_
  · intro C I q hq
    have : IsIso (DerivedCategory.Q.map q) := inferInstance
    exact inferInstanceAs (IsIso (F₀.rightDerivedFunctor.map (DerivedCategory.Q.map q)))
  · intro I hI
    dsimp only [η]
    rw [derivedUnit_iso]
    infer_instance
  · intro I hI
    change η.app I ≫ (ρ.comparison.hom.app I ≫ DerivedCategory.Q.map (𝟙 _)) = _
    erw [DerivedCategory.Q.map_id, Category.comp_id, ρ.computes]
    erw [derivedUnit_iso, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
    rfl
  · intro I hI r
    simp only [Functor.commShiftIso_comp_hom_app]
    erw [Category.assoc, ← DerivedCategory.Q.commShiftIso_hom_naturality,
      ← DerivedCategory.Q.map_comp_assoc, ← limitToRoos_shift l E W cs hcs,
      DerivedCategory.Q.map_comp]
    exact Category.assoc _ _ _

end WeilConjectures
