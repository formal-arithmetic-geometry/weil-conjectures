/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurStrictScalar.ScalarReductionTowerBalancing
public import WeilConjectures.SmoothPurity.PurStrictScalar.StrictScalarMateEvaluationData
public import WeilConjectures.SmoothPurity.PurStrictScalar.FiniteScalarCoordinateData

import all WeilConjectures.SmoothPurity.PurStrictScalar.FiniteScalarCoordinateData
import all WeilConjectures.SmoothPurity.Completed.CompletedIntegralFiniteFree
import all WeilConjectures.CategoryTheory.Constant.ConstantFiniteFreeSectionBasis
import all WeilConjectures.CategoryTheory.SmoothPurity.AdicBasisLimit
import all WeilConjectures.AlgebraicGeometry.VaryingRing.VaryingRingOperations
import WeilConjectures.SmoothPurity.PurStrictScalar.StrictScalarMateFiniteEvaluation
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
import WeilConjectures.SmoothPurity.PurStrictScalar.ProperBiproductCoordinate
import WeilConjectures.SmoothPurity.PurStrictScalar.StrictProperBiproductCoordinate

/-! # Finite scalar proper/open mate on strict compact-support reduction towers

Source: Stacks 07A6, 0B56, 0940 and 0E8I.
(blueprint: lem-pur-compact-support-strict-scalar-mate).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
attribute [local irreducible] AlgebraicGeometry.ProEtale.VaryingRing.exactAdj
attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.rightDerivedFunctor
attribute [local irreducible] CategoryTheory.Functor.rightDerivedFunctorIsoMapDerivedCategory
  CategoryTheory.Functor.mapDerivedCategoryCompIso
attribute [local irreducible] CategoryTheory.Limits.limit
attribute [local irreducible] AlgebraicGeometry.Scheme.pbcScalarAdjunction
  AlgebraicGeometry.Scheme.pbcDerivedScalarAdjunction
  WeilConjectures.PurCompactSupport.finiteChange
  WeilConjectures.PurCompactSupport.projection
attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategoryFactors
attribute [local irreducible] WeilConjectures.PurStrictScalar.ordinaryReduction
  WeilConjectures.PurStrictScalar.ordinaryReductionAdj
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale.StrictTower
open AlgebraicGeometry.ProEtale
namespace WeilConjectures.PurStrictScalar
attribute [local irreducible] AlgebraicGeometry.ProEtale.StrictTower.adj
  scalarAdj properRestriction

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
  (i : E →ₐ[ℚ_[l]] F)

/-- Restriction along any tower-index functor is exact on the entire diagram
category. Source: Stacks 0940
(blueprint: lem-pur-compact-support-strict-scalar-mate). -/
abbrev diagramRestriction (W : Scheme.{u}) (ρ : ℕᵒᵖ ⥤ ℕᵒᵖ) :=
  (Functor.whiskeringLeft ℕᵒᵖ ℕᵒᵖ
    (Modules (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) W)).obj ρ

/-- A family of quotient transitions is localized as a map between entire strict
diagrams. It is not a family of morphisms in separately formed derived categories.
Source: Stacks 0940 (blueprint: lem-pur-compact-support-strict-scalar-mate). -/
def diagramTransition (W : Scheme.{u}) {ρ σ : ℕᵒᵖ ⥤ ℕᵒᵖ} (α : ρ ⟶ σ) :
    (diagramRestriction l F W ρ).mapDerivedCategory ⟶
      (diagramRestriction l F W σ).mapDerivedCategory :=
  Localization.liftNatTrans DerivedCategory.Q
    (HomologicalComplex.quasiIso
      (Towers (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) W) (.up ℤ))
    _ _ (diagramRestriction l F W ρ).mapDerivedCategory
    (diagramRestriction l F W σ).mapDerivedCategory
    (Functor.whiskerRight (NatTrans.mapHomologicalComplex
      ((Functor.whiskeringLeft ℕᵒᵖ ℕᵒᵖ
        (Modules (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) W)).map α)
      (.up ℤ)) DerivedCategory.Q)

/-- Quotient-transition squares commute inside the derived category of strict
towers, for every family of comparable tower indices, before any derived limit.
Constant index functors give each individual quotient-transition square.
Source: Stacks 0940 (blueprint: lem-pur-compact-support-strict-scalar-mate).
Proof: the ordinary index transition is a natural transformation of exact
endofunctors on strict diagrams. Its localization is still natural on the
ordinary derived category of those diagrams. Apply this naturality to the
constructed whole-diagram arrow, before evaluation or inverse limits. -/
theorem arrow_transition {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (S : CoefficientDerivedSystemCalculus.{u, u} l E X)
    (S' : CoefficientDerivedSystemCalculus.{u, u} l F X) (e : ℕ)
    (he : PurCompactSupport.Ramification l E F i e) (hepos : 1 ≤ e)
    (M : DerivedCategory (scalarReductionSource l E X))
    (ρ σ : ℕᵒᵖ ⥤ ℕᵒᵖ) (α : ρ ⟶ σ) :
    (diagramRestriction l F Y ρ).mapDerivedCategory.map
          ((arrow l E F i c S S' e he hepos).app M) ≫
        (diagramTransition l F Y α).app
          ((pbcDerivedExtend (completedCoefficientMap l E F i X) ⋙
            support l F c S' ⋙ subsequence l F Y e).obj M) =
      (diagramTransition l F Y α).app ((support l E c S ⋙ T l E F i Y).obj M) ≫
        (diagramRestriction l F Y σ).mapDerivedCategory.map
          ((arrow l E F i c S S' e he hepos).app M) := by
  exact (diagramTransition l F Y α).naturality
    ((arrow l E F i c S S' e he hepos).app M)

/-- The canonical pullback/tensor balancing square on whole strict towers, fixed
by the normalized scalar and geometric composite adjunctions.
Source: Stacks 07A6, 0B56 (blueprint: lem-pur-compact-support-strict-scalar-mate). -/
def strictScalarPull {Z W : Scheme.{u}} (g : Z ⟶ W) :
    G (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) g ⋙ T l E F i Z ≅
      T l E F i W ⋙ G (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) g :=
  (((adj (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) g).comp
    (scalarAdj l E F i Z)).ofNatIsoRight (properRestriction l E F i g).symm).leftAdjointUniq
      ((scalarAdj l E F i W).comp
        (adj (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) g))

private theorem leftAdjointUniq_ofNatIsoRight_inv
    {A B : Type*} [Category A] [Category B]
    {L L' : A ⥤ B} {U U' : B ⥤ A}
    (a : L ⊣ U) (b : L' ⊣ U') (δ : U ≅ U') :
    (a.ofNatIsoRight δ |>.leftAdjointUniq b).inv =
      (conjugateEquiv a b).symm δ.hom := by
  ext N
  simp [Adjunction.leftAdjointUniq, conjugateEquiv_symm_apply_app,
    Adjunction.ofNatIsoRight_unit]

private theorem scalarMate_geometric_transpose
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {LA : A ⥤ B} {RA : B ⥤ A} {TZ : B ⥤ D} {UZ : D ⥤ B}
    {TW : A ⥤ C} {UW : C ⥤ A} {LB : C ⥤ D} {RB : D ⥤ C}
    (a : LA ⊣ RA) (b : TZ ⊣ UZ) (c : TW ⊣ UW) (d : LB ⊣ RB)
    (δ : UZ ⋙ RA ≅ RB ⋙ UW) (N : B) :
    (d.homEquiv _ _).symm
        (((mateEquiv b c).symm (TwoSquare.mk _ _ _ _ δ.hom)).app N) =
      ((conjugateEquiv (a.comp b) (c.comp d)).symm δ.hom).app (RA.obj N) ≫
        TZ.map (a.counit.app N) := by
  let μ : TwoSquare TW LA LB TZ :=
    TwoSquare.mk _ _ _ _ ((conjugateEquiv (a.comp b) (c.comp d)).symm δ.hom)
  have hm : mateEquiv a d μ = (mateEquiv b c).symm
      (TwoSquare.mk _ _ _ _ δ.hom) := by
    apply (mateEquiv b c).injective
    rw [Equiv.apply_symm_apply]
    change (mateEquiv b c (mateEquiv a d μ)).natTrans = _
    rw [iterated_mateEquiv_conjugateEquiv]
    exact (conjugateEquiv (a.comp b) (c.comp d)).apply_symm_apply δ.hom
  have h := mateEquiv_counit a d μ N
  rw [hm] at h
  simpa [Adjunction.homEquiv_counit, μ] using h

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The strict proper mate has the geometric counit transpose before evaluation.
Source: Stacks 07A6, 0B56 (blueprint: lem-pur-compact-support-strict-scalar-mate).
Proof: unfold the normalized left-adjoint comparison and the scalar mate. Apply
the scalar and geometric triangle identities to the intermediate unit/counit pairs.
The remaining composite is balancing followed by scalar extension of the counit. -/
theorem strictProper_geometric_transpose {Z W : Scheme.{u}} (g : Z ⟶ W)
    (N : Derived (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) Z) :
    ((adj (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) g).homEquiv _ _).symm
        ((proper l E F i g).app N) =
      (strictScalarPull l E F i g).inv.app
          ((R (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) g).obj N) ≫
        (T l E F i Z).map
          ((adj (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) g).counit.app N) := by
  unfold proper
  rw [strictScalarPull, leftAdjointUniq_ofNatIsoRight_inv]
  exact scalarMate_geometric_transpose
    (adj (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) g)
    (scalarAdj l E F i Z) (scalarAdj l E F i W)
    (adj (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) g)
    (properRestriction l E F i g).symm N

/-- The ordinary base-site open tensor balancing, with its scalar/open-unit formula.
Source: Stacks 0E8I (blueprint: lem-pur-compact-support-strict-scalar-mate). -/
def ordinaryBaseOpenTensor {R S : PurCompactSupport.Coefficients.{u}}
    (a : PurCompactSupport.Change R S) {Z W : Scheme.{u}} (j : Z ⟶ W)
    [IsOpenImmersion j] :
    PurCompactSupport.openExtension R j ⋙ pbcExtend (a.map W) ⟶
      pbcExtend (a.map Z) ⋙ PurCompactSupport.openExtension S j :=
  ((mateEquiv (pbcScalarAdjunction (a.map Z))
    (pbcScalarAdjunction (a.map W))).symm
      (TwoSquare.mk _ _ _ _ (PurCompactSupport.openRestrictionMap a j))).natTrans

private theorem inverseDoubleMate_isIso
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {F₁ : A ⥤ B} {U₁ : B ⥤ A} {F₂ : C ⥤ D} {U₂ : D ⥤ C}
    {L₁ : A ⥤ C} {R₁ : C ⥤ A} {L₂ : B ⥤ D} {R₂ : D ⥤ B}
    (a : F₁ ⊣ U₁) (b : F₂ ⊣ U₂) (c : L₁ ⊣ R₁) (d : L₂ ⊣ R₂)
    (δ : R₂ ⋙ U₁ ≅ U₂ ⋙ R₁) :
    IsIso (((mateEquiv a b).symm ((mateEquiv d c).symm
      (TwoSquare.mk _ _ _ _ δ.hom))).natTrans) := by
  rw [iterated_mateEquiv_conjugateEquiv_symm]
  dsimp only [Equiv.trans_apply, TwoSquare.equivNatTrans]
  exact conjugateEquiv_symm_iso (a.comp d) (c.comp b) δ.hom

attribute [local irreducible] WeilConjectures.PurCompactSupport.openAdjunction
  AlgebraicGeometry.Scheme.proEtaleRingRestrictionPullbackInv in
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- Ordinary base-site open tensor balancing is an isomorphism.
Source: Stacks 0E8I (blueprint: lem-pur-compact-support-strict-scalar-mate).
Proof: localize at the open. The open-adjunction unit identifies the map with
identity on balanced tensors. Both sides vanish off the open. The same formula
constructs its inverse and is preserved by module sheafification. -/
theorem ordinaryBaseOpenTensor_isIso {R S : PurCompactSupport.Coefficients.{u}}
    (a : PurCompactSupport.Change R S) {Z W : Scheme.{u}} (j : Z ⟶ W)
    [IsOpenImmersion j] : IsIso (ordinaryBaseOpenTensor a j) := by
  have := proEtaleRingRestrictionPullbackInv_isIso
    j (R.ring W) (S.ring W) (R.ring Z) (S.ring Z)
      (a.map W) (a.map Z) (R.pull j) (S.pull j) (a.square j)
  let δ := (asIso (proEtaleRingRestrictionPullbackInv
    j (R.ring W) (S.ring W) (R.ring Z) (S.ring Z)
      (a.map W) (a.map Z) (R.pull j) (S.pull j) (a.square j))).symm
  unfold ordinaryBaseOpenTensor PurCompactSupport.openRestrictionMap
  exact inverseDoubleMate_isIso
    (pbcScalarAdjunction (a.map Z)) (pbcScalarAdjunction (a.map W))
    (PurCompactSupport.openAdjunction R j) (PurCompactSupport.openAdjunction S j) δ

/-- The ordinary open tensor comparison on whole strict diagrams. It is the mate
of the actual identity-on-open, zero-off-open scalar restriction comparison.
Source: Stacks 0E8I (blueprint: lem-pur-compact-support-strict-scalar-mate). -/
def ordinaryOpenTensor {Z W : Scheme.{u}} (j : Z ⟶ W) [IsOpenImmersion j] :
    towerJ (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) j ⋙ tensor l E F i W ⟶
      tensor l E F i Z ⋙ towerJ (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) j :=
  ((mateEquiv ((pbcScalarAdjunction (constantMap l E F i Z)).whiskerRight ℕᵒᵖ)
    ((pbcScalarAdjunction (constantMap l E F i W)).whiskerRight ℕᵒᵖ)).symm
      (TwoSquare.mk _ _ _ _ (openRestrictionOrdinary l E F i j).hom)).natTrans

/-- Ordinary open tensor balancing is invertible on all strict diagrams.
Source: Stacks 0E8I (blueprint: lem-pur-compact-support-strict-scalar-mate).
Proof: on the open both directions preserve each elementary tensor. Outside the
open both are zero. The balanced tensor universal property and module sheafification
give inverse maps, pointwise in the tower index. -/
theorem ordinaryOpenTensor_isIso {Z W : Scheme.{u}} (j : Z ⟶ W) [IsOpenImmersion j] :
    IsIso (ordinaryOpenTensor l E F i j) := by
  have := ordinaryBaseOpenTensor_isIso (change l E F i) j
  have h : ordinaryOpenTensor l E F i j =
      (Functor.whiskeringRight ℕᵒᵖ _ _).map
        (ordinaryBaseOpenTensor (change l E F i) j) := by
    ext M n
    rfl
  rw [h]
  infer_instance

private theorem exactAdj_eq_rightDerived
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B] [Abelian.HasKInjectiveResolutions B]
    {L : A ⥤ B} {P : B ⥤ A} [L.Additive] [P.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits P] [PreservesFiniteColimits P] (a : L ⊣ P) :
    a.mapDerivedCategoryRightDerivedAdjunction.ofNatIsoRight
      P.rightDerivedFunctorIsoMapDerivedCategory = VaryingRing.exactAdj a := by
  apply Adjunction.ext
  apply Localization.natTrans_ext DerivedCategory.Qh
    (HomotopyCategory.quasiIso A (.up ℤ))
  intro K
  apply (cancel_mono (P.mapDerivedCategory.map (L.mapDerivedCategoryFactorsh.hom.app K) ≫
    P.mapDerivedCategoryFactorsh.hom.app ((L.mapHomotopyCategory (.up ℤ)).obj K))).mp
  have hη := (a.mapHomotopyCategory (.up ℤ)).derivedη_fac_app
    (HomotopyCategory.quasiIso A (.up ℤ))
    L.mapDerivedCategoryFactorsh.hom P.rightDerivedFunctorUnit K
  have hn := P.rightDerivedFunctorIsoMapDerivedCategory.hom.naturality
    (L.mapDerivedCategoryFactorsh.hom.app K)
  have hr := congr_app P.rightDerivedFunctorIsoMapDerivedCategory_hom_fac
    ((L.mapHomotopyCategory (.up ℤ)).obj K)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app] at hr
  simp only [Adjunction.ofNatIsoRight_unit, NatTrans.comp_app,
    Functor.whiskerLeft_app]
  change (a.mapDerivedCategoryRightDerivedAdjunction.unit.app _ ≫
    P.rightDerivedFunctorIsoMapDerivedCategory.hom.app _) ≫ _ = _
  change a.mapDerivedCategoryRightDerivedAdjunction.unit.app _ ≫ _ = _ at hη
  rw [Category.assoc, ← reassoc_of% hn, ← Category.assoc, hη,
    Category.assoc, ← Category.assoc (P.rightDerivedFunctorUnit.app _) _ _, hr,
    Iso.inv_hom_id_app]
  erw [Category.comp_id]
  exact (VaryingRing.exactAdj_unit a K).symm


private theorem localizedInverseMate_eq
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory C] [HasDerivedCategory D]
    {L : A ⥤ B} {P : B ⥤ A} {L' : C ⥤ D} {P' : D ⥤ C}
    [L.Additive] [P.Additive] [L'.Additive] [P'.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    [PreservesFiniteLimits L'] [PreservesFiniteColimits L']
    [PreservesFiniteLimits P'] [PreservesFiniteColimits P']
    (a : L ⊣ P) (b : L' ⊣ P') {E : A ⥤ C} {E' : B ⥤ D}
    [E.Additive] [E'.Additive]
    [PreservesFiniteLimits E] [PreservesFiniteColimits E]
    [PreservesFiniteLimits E'] [PreservesFiniteColimits E']
    (d : P ⋙ E ≅ E' ⋙ P') (β : E ⋙ L' ≅ L ⋙ E')
    (hb : ∀ M, b.unit.app (E.obj M) ≫ P'.map (β.hom.app M) =
      E.map (a.unit.app M) ≫ d.hom.app (L.obj M)) :
    ((mateEquiv (VaryingRing.exactAdj a) (VaryingRing.exactAdj b)).symm
      (Functor.mapDerivedCategorySquareIso d).hom).natTrans =
        (Functor.mapDerivedCategorySquareIso β).hom := by
  have hd := VaryingRing.exactDerivedMate a b d β hb
  ext M
  apply ((VaryingRing.exactAdj b).homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  exact (unit_mateEquiv_symm (VaryingRing.exactAdj a) (VaryingRing.exactAdj b)
    (Functor.mapDerivedCategorySquareIso d).hom M).symm.trans (hd M).symm

/-- The open strict scalar mate is exactly ordinary tensor balancing localized.
Source: Stacks 0E8I, 07A6 (blueprint: lem-pur-compact-support-strict-scalar-mate).
Proof: exact localization descends the ordinary scalar and open adjunction units.
The mate formula, localization factors and triangle identities identify the maps. -/
theorem openTensor_ordinary {Z W : Scheme.{u}} (j : Z ⟶ W) [IsOpenImmersion j] :
    openTensor l E F i j =
      (Functor.mapDerivedCategorySquareIso
        (@asIso _ _ _ _ (ordinaryOpenTensor l E F i j)
          (ordinaryOpenTensor_isIso l E F i j))).hom := by
  let a := (pbcScalarAdjunction (constantMap l E F i Z)).whiskerRight ℕᵒᵖ
  let b := (pbcScalarAdjunction (constantMap l E F i W)).whiskerRight ℕᵒᵖ
  let d := openRestrictionOrdinary l E F i j
  let β := @asIso _ _ _ _ (ordinaryOpenTensor l E F i j)
    (ordinaryOpenTensor_isIso l E F i j)
  have hb (M : Towers (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) Z) :
      b.unit.app ((towerJ (ULift.{u + 1}
        (Padic.coefficientExtensionIntegers l E)) j).obj M) ≫
        (restrict l E F i W).map (β.hom.app M) =
      (towerJ (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) j).map
        (a.unit.app M) ≫ d.hom.app ((tensor l E F i Z).obj M) :=
    (unit_mateEquiv_symm a b d.hom M).symm
  unfold openTensor scalarAdj
  change ((mateEquiv
    (a.mapDerivedCategoryRightDerivedAdjunction.ofNatIsoRight
      (restrict l E F i Z).rightDerivedFunctorIsoMapDerivedCategory)
    (b.mapDerivedCategoryRightDerivedAdjunction.ofNatIsoRight
      (restrict l E F i W).rightDerivedFunctorIsoMapDerivedCategory)).symm
        (Functor.mapDerivedCategorySquareIso d).hom).natTrans =
    (Functor.mapDerivedCategorySquareIso β).hom
  rw [exactAdj_eq_rightDerived, exactAdj_eq_rightDerived]
  exact localizedInverseMate_eq a b d β hb


/-- The pasted restriction square, with ordinary open normalization followed by
the normalized derived proper square. Source: Stacks 07A6, 0B56
(blueprint: lem-pur-compact-support-strict-scalar-mate). -/
def pastedRestriction {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    U l E F i X ⋙ image l E c ≅ image l F c ⋙ U l E F i Y :=
  Functor.isoWhiskerRight (openRestriction l E F i c.i)
      (R (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) c.g) ≪≫
    Functor.isoWhiskerLeft
      (J (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) c.i)
      (properRestriction l E F i c.g).symm

/-- The ordered proper/open factorization is the scalar mate of the pasted square.
Only pasting of squares is used: no right-adjoint interpretation of j shriek.
Source: Stacks 07A6, 0B56 (blueprint: lem-pur-compact-support-strict-scalar-mate).
Proof: expand the two scalar mates. Naturality moves the intermediate unit and
counit past each square; the intermediate triangle identity cancels them. The
remaining composite is exactly the mate of the pasted restriction square. -/
theorem comparison_pasted {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    comparison l E F i c =
      ((mateEquiv (scalarAdj l E F i X) (scalarAdj l E F i Y)).symm
        (TwoSquare.mk _ _ _ _ (pastedRestriction l E F i c).hom)).natTrans := by
  let α := TwoSquare.mk _ _ _ _ (openRestriction l E F i c.i).hom
  let β := TwoSquare.mk _ _ _ _ (properRestriction l E F i c.g).inv
  let adjX := scalarAdj l E F i X
  let adjZ := scalarAdj l E F i c.Z
  let adjY := scalarAdj l E F i Y
  have hv : TwoSquare.vComp α β = (pastedRestriction l E F i c).hom := by
    ext N
    simp only [TwoSquare.vComp, α, β, pastedRestriction, TwoSquare.mk, TwoSquare.natTrans,
      Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom,
      Functor.isoWhiskerLeft_hom, NatTrans.comp_app, Functor.associator_inv_app,
      Functor.associator_hom_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Category.id_comp, Category.comp_id]
  have h := mateEquiv_vcomp adjX adjZ adjY
    ((mateEquiv adjX adjZ).symm α) ((mateEquiv adjZ adjY).symm β)
  simp only [Equiv.apply_symm_apply, hv] at h
  ext N
  have h' := congrArg (fun t ↦ ((mateEquiv adjX adjY).symm t).app N) h
  simpa only [Equiv.symm_apply_apply, α, β, adjX, adjZ, adjY,
    comparison, image, proper, openTensor, TwoSquare.hComp, TwoSquare.mk,
    TwoSquare.natTrans, NatTrans.comp_app, Functor.associator_inv_app,
    Functor.associator_hom_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Category.id_comp, Category.comp_id] using h'


section BasisTransport
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] AlgebraicGeometry.Scheme.proEtaleRingModuleAdjunction
  AlgebraicGeometry.Scheme.proEtaleRingModulePullback

private abbrev geometric_ring_map {Z W : Scheme.{u}} (g : Z ⟶ W)
    (R : Sheaf (ProEt.topology W) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology Z) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj R ≅ S) :
    (adicLisseForget W).obj R ⟶
      ((proEtaleBaseChange g).sheafPushforwardContinuous RingCat.{u + 1}
        (ProEt.topology W) (ProEt.topology Z)).obj ((adicLisseForget Z).obj S) :=
  ⟨Functor.whiskerRight (proEtaleRingDirectImageMap g R S c).hom
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩

private theorem geometric_unit_iso {Z W : Scheme.{u}} (g : Z ⟶ W)
    (R : Sheaf (ProEt.topology W) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology Z) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj R ≅ S) :
    IsIso (((proEtaleRingModuleAdjunction g R S c).homEquiv _ _).symm
      (SheafOfModules.unitToPushforwardObjUnit (geometric_ring_map g R S c))) := by
  let φ := geometric_ring_map g R S c
  let a := proEtaleRingModuleAdjunction g R S c
  have : (SheafOfModules.pushforward.{u + 1} φ).IsRightAdjoint := a.isRightAdjoint
  let b := SheafOfModules.pullbackPushforwardAdjunction.{u + 1} φ
  have h : (a.homEquiv _ _).symm (SheafOfModules.unitToPushforwardObjUnit φ) =
      (a.leftAdjointUniq b).hom.app _ ≫ SheafOfModules.pullbackObjUnitToUnit φ := by
    apply (a.homEquiv _ _).injective
    erw [Equiv.apply_symm_apply, a.homEquiv_naturality_right,
      Adjunction.homEquiv_leftAdjointUniq_hom_app]
    change SheafOfModules.unitToPushforwardObjUnit φ =
      (SheafOfModules.pullbackPushforwardAdjunction φ).homEquiv _ _
        (SheafOfModules.pullbackObjUnitToUnit φ)
    exact (SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit φ).symm
  erw [h]
  infer_instance

private theorem transported_basis
    {A B : Type*} [Category A] [Category B] {L : A ⥤ B} {P : B ⥤ A}
    (a : L ⊣ P) {I : Type} [HasProductsOfShape I A] [HasProductsOfShape I B]
    [PreservesLimitsOfShape (Discrete I) L]
    {X X' : A} {Y Y' : B} (k : L.obj X ≅ Y) (k' : L.obj X' ≅ Y')
    (b : (∏ᶜ fun _ : I ↦ X) ≅ X') :
    ∃! c : (∏ᶜ fun _ : I ↦ Y) ≅ Y',
      ∀ j : I,
        (a.homEquiv _ _ k'.hom) ≫ P.map (c.inv ≫ Pi.π (fun _ : I ↦ Y) j) =
          (b.inv ≫ Pi.π (fun _ : I ↦ X) j) ≫ a.homEquiv _ _ k.hom := by
  let t : L.obj (∏ᶜ fun _ : I ↦ X) ≅ (∏ᶜ fun _ : I ↦ Y) :=
    PreservesProduct.iso L (fun _ : I ↦ X) ≪≫ Pi.mapIso (fun _ : I ↦ k)
  let c := t.symm ≪≫ L.mapIso b ≪≫ k'
  have hc (j : I) :
      k'.hom ≫ c.inv ≫ Pi.π (fun _ : I ↦ Y) j =
        L.map (b.inv ≫ Pi.π (fun _ : I ↦ X) j) ≫ k.hom := by
    simp only [c, Iso.trans_inv, Iso.symm_inv, Functor.mapIso_inv,
      Category.assoc, Iso.hom_inv_id_assoc]
    simp only [t, Iso.trans_hom, PreservesProduct.iso_hom, Category.assoc,
      Pi.mapIso_hom_π, piComparison_comp_π_assoc, Functor.map_comp]
  have hc' (j : I) :
      (a.homEquiv _ _ k'.hom) ≫ P.map (c.inv ≫ Pi.π (fun _ : I ↦ Y) j) =
        (b.inv ≫ Pi.π (fun _ : I ↦ X) j) ≫ a.homEquiv _ _ k.hom := by
    rw [← a.homEquiv_naturality_right, ← a.homEquiv_naturality_left]
    exact congrArg (a.homEquiv _ _) (hc j)
  refine ⟨c, hc', ?_⟩
  intro c' hc''
  apply Iso.ext_inv
  apply Pi.hom_ext
  intro j
  apply (cancel_epi k'.hom).mp
  apply (a.homEquiv _ _).injective
  rw [a.homEquiv_naturality_right, a.homEquiv_naturality_right]
  exact (hc'' j).trans (hc' j).symm


/-- A finite basis on the target coefficient sheaf has a unique pulled-back basis
on the source, characterized on every coordinate after direct image of rings.
Source: Stacks 03CY, 03D8 (blueprint: lem-pur-compact-support-strict-scalar-mate).
Proof: pull back the global basis inclusions and projections by the exact inverse
image. The coefficient identifications identify the pulled-back regular modules
with the given regular modules. Their inverse identities survive inverse image.
The displayed formula is the inverse-image adjunction identity for the coordinate
maps; adjunction uniqueness determines the pulled-back basis. -/
theorem pulledBasis_existsUnique {R S : PurCompactSupport.Coefficients.{u}}
    (a : PurCompactSupport.Change R S) {Z W : Scheme.{u}} (g : Z ⟶ W) (d : ℕ)
    (bW : (∏ᶜ fun _ : Fin d ↦ SheafOfModules.unit ((adicLisseForget W).obj (R.ring W))) ≅
      (pbcRestrict (a.map W)).obj
        (SheafOfModules.unit ((adicLisseForget W).obj (S.ring W)))) :
    ∃! bZ : (∏ᶜ fun _ : Fin d ↦
        SheafOfModules.unit ((adicLisseForget Z).obj (R.ring Z))) ≅
        (pbcRestrict (a.map Z)).obj
          (SheafOfModules.unit ((adicLisseForget Z).obj (S.ring Z))),
      ∀ (V : W.ProEtᵒᵖ) (s : (S.ring W).obj.obj V) (j : Fin d),
        ((bZ.inv ≫ Pi.π (fun _ : Fin d ↦
            SheafOfModules.unit ((adicLisseForget Z).obj (R.ring Z))) j).val.app
              ((proEtaleBaseChange g).op.obj V))
            (((proEtaleRingDirectImageMap g (S.ring W) (S.ring Z) (S.pull g)).hom.app V) s) =
          ((proEtaleRingDirectImageMap g (R.ring W) (R.ring Z) (R.pull g)).hom.app V)
            (((bW.inv ≫ Pi.π (fun _ : Fin d ↦
              SheafOfModules.unit ((adicLisseForget W).obj (R.ring W))) j).val.app V) s) := by
  let φR := geometric_ring_map g (R.ring W) (R.ring Z) (R.pull g)
  let φS := geometric_ring_map g (S.ring W) (S.ring Z) (S.pull g)
  let aR := proEtaleRingModuleAdjunction g (R.ring W) (R.ring Z) (R.pull g)
  let aS := proEtaleRingModuleAdjunction g (S.ring W) (S.ring Z) (S.pull g)
  let uR := SheafOfModules.unitToPushforwardObjUnit φR
  let uS := SheafOfModules.unitToPushforwardObjUnit φS
  let UW := pbcRestrict (a.map W)
  let UZ := pbcRestrict (a.map Z)
  let δ := proEtaleRingRestrictionPullbackInv g
    (R.ring W) (S.ring W) (R.ring Z) (S.ring Z)
    (a.map W) (a.map Z) (R.pull g) (S.pull g) (a.square g)
  let δ' := proEtaleRingRestrictionDirectImage g
    (R.ring W) (S.ring W) (R.ring Z) (S.ring Z)
    (a.map W) (a.map Z) (R.pull g) (S.pull g) (a.square g)
  have : IsIso δ := proEtaleRingRestrictionPullbackInv_isIso g
    (R.ring W) (S.ring W) (R.ring Z) (S.ring Z)
    (a.map W) (a.map Z) (R.pull g) (S.pull g) (a.square g)
  have : IsIso ((aR.homEquiv _ _).symm uR) :=
    geometric_unit_iso g (R.ring W) (R.ring Z) (R.pull g)
  have : IsIso ((aS.homEquiv _ _).symm uS) :=
    geometric_unit_iso g (S.ring W) (S.ring Z) (S.pull g)
  let k := asIso ((aR.homEquiv _ _).symm uR)
  let kS := asIso ((aS.homEquiv _ _).symm uS)
  let k' := (asIso δ).app (SheafOfModules.unit ((adicLisseForget W).obj (S.ring W))) ≪≫
    UZ.mapIso kS
  let v := UW.map uS ≫ δ'.hom.app (SheafOfModules.unit ((adicLisseForget Z).obj (S.ring Z)))
  have hk' : aR.homEquiv _ _ k'.hom = v := by
    let SW := SheafOfModules.unit ((adicLisseForget W).obj (S.ring W))
    let PA := proEtaleRingModuleDirectImage g (R.ring W) (R.ring Z) (R.pull g)
    have hδ' : δ.app SW = (aR.homEquiv _ _).symm
        (UW.map (aS.unit.app SW) ≫
          δ'.hom.app ((proEtaleRingModulePullback g
            (S.ring W) (S.ring Z) (S.pull g)).obj SW)) := by
      dsimp only [δ, proEtaleRingRestrictionPullbackInv]
      simp only [proEtaleRingRestrictionPullbackApp, Adjunction.homEquiv_counit,
        Functor.map_comp, Category.assoc]
      rfl
    have hδ : aR.unit.app (UW.obj SW) ≫ PA.map (δ.app SW) =
        UW.map (aS.unit.app SW) ≫
          δ'.hom.app ((proEtaleRingModulePullback g
            (S.ring W) (S.ring Z) (S.pull g)).obj SW) := by
      change aR.homEquiv _ _ (δ.app SW) = _
      erw [hδ']
      exact (aR.homEquiv _ _).apply_symm_apply _
    change aR.unit.app _ ≫ PA.map (δ.app SW ≫ UZ.map kS.hom) = v
    rw [Functor.map_comp, ← Category.assoc]
    erw [hδ, Category.assoc, ← δ'.hom.naturality kS.hom,
      ← Category.assoc, ← UW.map_comp]
    have hS : aS.unit.app _ ≫
        (proEtaleRingModuleDirectImage g (S.ring W) (S.ring Z) (S.pull g)).map kS.hom =
          uS := by
      exact (aS.homEquiv _ _).apply_symm_apply uS
    rw [hS]
    rfl
  obtain ⟨bZ, hbZ, huniq⟩ := transported_basis aR k k' bW
  have hk : aR.homEquiv _ _ k.hom = uR := (aR.homEquiv _ _).apply_symm_apply uR
  simp only [hk, hk'] at hbZ huniq
  have hv (V : W.ProEtᵒᵖ) (s : (S.ring W).obj.obj V) :
      v.val.app V s =
        (proEtaleRingDirectImageMap g (S.ring W) (S.ring Z) (S.pull g)).hom.app V s := by
    exact (proEtaleRingRestrictionDirectImage_existsUnique g
      (R.ring W) (S.ring W) (R.ring Z) (S.ring Z)
      (a.map W) (a.map Z) (R.pull g) (S.pull g) (a.square g)).choose_spec.1 _ V _
  refine ⟨bZ, ?_, ?_⟩
  · intro V s j
    have h := congrArg (fun z ↦ z.val.app V s) (hbZ j)
    change ((bZ.inv ≫ Pi.π _ j).val.app ((proEtaleBaseChange g).op.obj V))
      (v.val.app V s) = _ at h
    rw [hv] at h
    exact h
  · intro bZ' hbZ'
    apply huniq bZ'
    intro j
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro V
    ext s
    change ((bZ'.inv ≫ Pi.π _ j).val.app ((proEtaleBaseChange g).op.obj V))
      (v.val.app V s) = _
    erw [hv]
    exact hbZ' V s j

end BasisTransport


/-- The uniquely transported coefficient basis; this affects only coordinates,
not the definition of the scalar mate. Source: Stacks 03D8
(blueprint: lem-pur-compact-support-strict-scalar-mate). -/
def pulledBasis {R S : PurCompactSupport.Coefficients.{u}}
    (a : PurCompactSupport.Change R S) {Z W : Scheme.{u}} (g : Z ⟶ W) (d : ℕ)
    (bW : (∏ᶜ fun _ : Fin d ↦ SheafOfModules.unit ((adicLisseForget W).obj (R.ring W))) ≅
      (pbcRestrict (a.map W)).obj
        (SheafOfModules.unit ((adicLisseForget W).obj (S.ring W)))) :=
  (pulledBasis_existsUnique a g d bW).choose

attribute [local irreducible] pulledBasis

/-- Exact localization of the actual ordinary open tensor map for any finite basis.
Source: Stacks 0E8I (blueprint: lem-pur-compact-support-strict-scalar-mate). -/
def baseOpenExactNormalization {R S : PurCompactSupport.Coefficients.{u}}
    (a : PurCompactSupport.Change R S) {Z W : Scheme.{u}} (j : Z ⟶ W)
    [IsOpenImmersion j] (d : ℕ)
    (bW : (∏ᶜ fun _ : Fin d ↦ SheafOfModules.unit ((adicLisseForget W).obj (R.ring W))) ≅
      (pbcRestrict (a.map W)).obj
        (SheafOfModules.unit ((adicLisseForget W).obj (S.ring W)))) :
    (PurCompactSupport.openExtension R j).mapDerivedCategory ⋙ pbcDerivedExtend (a.map W) ≅
      pbcDerivedExtend (a.map Z) ⋙ (PurCompactSupport.openExtension S j).mapDerivedCategory :=
  haveI := (finiteScalar_exact W (a.map W) d bW).1
  haveI := (finiteScalar_exact W (a.map W) d bW).2
  haveI := (finiteScalar_exact Z (a.map Z) d (pulledBasis a j d bW)).1
  haveI := (finiteScalar_exact Z (a.map Z) d (pulledBasis a j d bW)).2
  haveI := ordinaryBaseOpenTensor_isIso a j
  -- Compare the exact and universal derived scalar pairs using the scalar adjunction.
  Functor.isoWhiskerLeft (PurCompactSupport.openExtension R j).mapDerivedCategory
      (((pbcScalarAdjunction (a.map W)).mapDerivedCategoryRightDerivedAdjunction.ofNatIsoRight
        (pbcRestrict (a.map W)).rightDerivedFunctorIsoMapDerivedCategory).leftAdjointUniq
          (pbcDerivedScalarAdjunction (a.map W))).symm ≪≫
    Functor.mapDerivedCategorySquareIso (asIso (ordinaryBaseOpenTensor a j)) ≪≫
    Functor.isoWhiskerRight
      (((pbcScalarAdjunction (a.map Z)).mapDerivedCategoryRightDerivedAdjunction.ofNatIsoRight
        (pbcRestrict (a.map Z)).rightDerivedFunctorIsoMapDerivedCategory).leftAdjointUniq
          (pbcDerivedScalarAdjunction (a.map Z))) _

private theorem inverseMate_transportLeft
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L L' : A ⥤ B} {R : B ⥤ A} {K K' : C ⥤ D} {S : D ⥤ C}
    (a : L ⊣ R) (a' : L' ⊣ R) (b : K ⊣ S) (b' : K' ⊣ S)
    {G : A ⥤ C} {H : B ⥤ D} (β : R ⋙ G ⟶ H ⋙ S) :
    ((mateEquiv a' b').symm (TwoSquare.mk _ _ _ _ β)).natTrans =
      Functor.whiskerLeft G (b.leftAdjointUniq b').inv ≫
        ((mateEquiv a b).symm (TwoSquare.mk _ _ _ _ β)).natTrans ≫
          Functor.whiskerRight (a.leftAdjointUniq a').hom H := by
  ext M
  apply (b'.homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.map_comp]
  have hb : b'.unit.app (G.obj M) ≫ S.map ((b.leftAdjointUniq b').inv.app (G.obj M)) =
      b.unit.app (G.obj M) := by
    rw [Adjunction.leftAdjointUniq_inv_app]
    exact Adjunction.unit_leftAdjointUniq_hom_app _ _ _
  rw [← Category.assoc, ← Category.assoc, hb]
  have h₁ := unit_mateEquiv_symm a b (TwoSquare.mk _ _ _ _ β) M
  have h₂ := unit_mateEquiv_symm a' b' (TwoSquare.mk _ _ _ _ β) M
  dsimp only [TwoSquare.mk, TwoSquare.natTrans, Functor.id_obj] at h₁ h₂
  rw [← h₁, ← h₂]
  have hn := β.naturality ((a.leftAdjointUniq a').hom.app M)
  change G.map (R.map _) ≫ β.app _ = β.app _ ≫ S.map (H.map _) at hn
  rw [Category.assoc, ← hn, ← G.map_comp_assoc,
    Adjunction.unit_leftAdjointUniq_hom_app]

/-- In every finite coefficient basis, the finite derived open map is ordinary
extension-by-zero tensor balancing with the universal scalar normalization.
Source: Stacks 0E8I, 07A6 (blueprint: lem-pur-compact-support-strict-scalar-mate).
Proof: the exact ordinary scalar adjunction and the universal derived scalar
adjunction are identified by their common tensor-unit normalization. Localization
preserves the open-unit square and the mate formula. The displayed conjugate is
therefore the recorded derived open comparison, independently of the chosen basis. -/
theorem open_base_ordinary {R S : PurCompactSupport.Coefficients.{u}}
    (a : PurCompactSupport.Change R S) {Z W : Scheme.{u}} (j : Z ⟶ W)
    [IsOpenImmersion j] (d : ℕ)
    (bW : (∏ᶜ fun _ : Fin d ↦ SheafOfModules.unit ((adicLisseForget W).obj (R.ring W))) ≅
      (pbcRestrict (a.map W)).obj
        (SheafOfModules.unit ((adicLisseForget W).obj (S.ring W)))) :
    PurCompactSupport.openComparison a j = (baseOpenExactNormalization a j d bW).hom := by
  have := (finiteScalar_exact W (a.map W) d bW).1
  have := (finiteScalar_exact W (a.map W) d bW).2
  have := (finiteScalar_exact Z (a.map Z) d (pulledBasis a j d bW)).1
  have := (finiteScalar_exact Z (a.map Z) d (pulledBasis a j d bW)).2
  have := ordinaryBaseOpenTensor_isIso a j
  let aZ := pbcScalarAdjunction (a.map Z)
  let aW := pbcScalarAdjunction (a.map W)
  let δ := asIso (PurCompactSupport.openRestrictionMap a j)
  let β := asIso (ordinaryBaseOpenTensor a j)
  have hb (M : pbcModules Z (R.ring Z)) :
      aW.unit.app ((PurCompactSupport.openExtension R j).obj M) ≫
        (pbcRestrict (a.map W)).map (β.hom.app M) =
      (PurCompactSupport.openExtension R j).map (aZ.unit.app M) ≫
        δ.hom.app ((pbcExtend (a.map Z)).obj M) :=
    (unit_mateEquiv_symm aZ aW δ.hom M).symm
  have hm : ((mateEquiv (VaryingRing.exactAdj aZ) (VaryingRing.exactAdj aW)).symm
        (Functor.mapDerivedCategorySquareIso δ).hom).natTrans =
      (Functor.mapDerivedCategorySquareIso β).hom := by
    exact localizedInverseMate_eq aZ aW δ β hb
  unfold PurCompactSupport.openComparison baseOpenExactNormalization
  rw [exactAdj_eq_rightDerived, exactAdj_eq_rightDerived]
  change ((mateEquiv (pbcDerivedScalarAdjunction (a.map Z))
    (pbcDerivedScalarAdjunction (a.map W))).symm
      (Functor.mapDerivedCategorySquareIso δ).hom).natTrans = _
  have ht := inverseMate_transportLeft (VaryingRing.exactAdj aZ)
    (pbcDerivedScalarAdjunction (a.map Z)) (VaryingRing.exactAdj aW)
    (pbcDerivedScalarAdjunction (a.map W)) (Functor.mapDerivedCategorySquareIso δ).hom
  rw [hm] at ht
  exact ht

/-- In any finite basis the restricted proper mate is the canonical finite-product
(and hence biproduct) comparison. All coordinates are fixed on ordinary pure tensors
and on every derived counit, so the assertion does not allow unrelated isomorphisms.
It applies to every finite A_n-basis of B_n as well as constant integral coefficients.
Source: Stacks 0B56, 0944 (blueprint: lem-pur-compact-support-strict-scalar-mate).
Proof: transpose each coordinate column under the geometric adjunction. Ordinary
balancing sends that basis tensor to the same basis inclusion after the proper
counit. The triangle identity identifies its adjunct with direct image of the
inclusion. Projecting proves the displayed finite-product comparison identity.
The pure-tensor and whole-cochain normalizations of derivedCoordinates ensure this
is an equality for the specified scalar functor and canonical mate. -/
theorem proper_biproduct {R S : PurCompactSupport.Coefficients.{u}}
    (a : PurCompactSupport.Change R S) {Z W : Scheme.{u}} (g : Z ⟶ W) (d : ℕ)
    (bW : (∏ᶜ fun _ : Fin d ↦ SheafOfModules.unit ((adicLisseForget W).obj (R.ring W))) ≅
      (pbcRestrict (a.map W)).obj
        (SheafOfModules.unit ((adicLisseForget W).obj (S.ring W))))
    (N : DerivedCategory (pbcModules Z (R.ring Z))) :
    (pbcDerivedRestrict (a.map W)).map ((PurCompactSupport.properComparison a g).app N) ≫
        (proEtaleRingRestrictionDerivedDirectImage g
          (R.ring W) (S.ring W) (R.ring Z) (S.ring Z)
          (a.map W) (a.map Z) (R.pull g) (S.pull g) (a.square g)).hom.app
            ((pbcDerivedExtend (a.map Z)).obj N) ≫
        (proEtaleRingDerivedDirectImage g (R.ring W) (R.ring Z) (R.pull g)).map
          ((derivedCoordinates Z (a.map Z) d (pulledBasis a g d bW)).hom.app N) ≫
        piComparison
          (proEtaleRingDerivedDirectImage g (R.ring W) (R.ring Z) (R.pull g))
          (fun _ : Fin d ↦ N) =
      (derivedCoordinates W (a.map W) d bW).hom.app
        ((proEtaleRingDerivedDirectImage g (R.ring W) (R.ring Z) (R.pull g)).obj N) := by
  apply Pi.hom_ext
  intro j
  simpa only [Category.assoc] using
    proper_biproduct_coordinate a g d bW (pulledBasis a g d bW) N j

/-- The restricted strict proper mate is the canonical finite-biproduct comparison
in every basis, with coordinates normalized on whole diagram complexes.
Source: Stacks 0B56, 0940, 0944
(blueprint: lem-pur-compact-support-strict-scalar-mate).
Proof: ordinary tower coordinates use the same basis at every level. Transpose
its basis columns under the whole-tower geometric adjunction. Balancing and the
proper counit give direct image of those inclusions. Their projections give the
canonical product comparison identity below. This argument is made in the derived
diagram category; no equality is inferred from evaluated derived maps. -/
theorem strictProper_biproduct {Z W : Scheme.{u}} (g : Z ⟶ W) (d : ℕ)
    (bW : (∏ᶜ fun _ : Fin d ↦
        SheafOfModules.unit ((adicLisseForget W).obj ((constants l E).ring W))) ≅
      (pbcRestrict (constantMap l E F i W)).obj
        (SheafOfModules.unit ((adicLisseForget W).obj ((constants l F).ring W))))
    (N : Derived (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) Z) :
    (U l E F i W).map ((proper l E F i g).app N) ≫
        (properRestriction l E F i g).hom.app ((T l E F i Z).obj N) ≫
        (R (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) g).map
          ((derivedTowerCoordinates Z (constantMap l E F i Z) d
            (pulledBasis (change l E F i) g d bW)).hom.app N) ≫
        piComparison (R (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) g)
          (fun _ : Fin d ↦ N) =
      (derivedTowerCoordinates W (constantMap l E F i W) d bW).hom.app
        ((R (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) g).obj N) := by
  apply Pi.hom_ext
  intro j
  simpa only [Category.assoc] using
    strictProper_biproduct_coordinate l E F i g d bW
      (pulledBasis (change l E F i) g d bW)
      (by
        intro V s r
        unfold pulledBasis
        convert (pulledBasis_existsUnique (change l E F i) g d bW).choose_spec.1 V s r
          using 1 <;> rfl) N j

section MateInvertibility
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

private theorem exactDerived_reflectsIsomorphisms
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    (V : A ⥤ B) [V.Additive] [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    [V.ReflectsIsomorphisms] : V.mapDerivedCategory.ReflectsIsomorphisms := by
  refine ⟨fun f _ ↦ ?_⟩
  rw [DerivedCategory.isIso_iff]
  intro n
  have : IsIso (V.map ((DerivedCategory.homologyFunctor _ n).map f)) :=
    (NatIso.isIso_map_iff (V.mapDerivedCategoryHomologyFunctorIso n) f).2
      (by rw [Functor.comp_map]; infer_instance)
  exact isIso_of_reflects_iso _ V

private theorem constant_basis (W : Scheme.{u})
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    (d : ℕ) (b : Module.Basis (Fin d) A B) :
    Nonempty ((∏ᶜ fun _ : Fin d ↦ SheafOfModules.unit
        ((adicLisseForget W).obj (proEtaleConstantRing W A))) ≅
      (pbcRestrict ((constantSheaf (ProEt.topology W) CommRingCat.{u + 1}).map
        (CommRingCat.ofHom (algebraMap A B).ulift.{u + 1, u + 1}))).obj
          (SheafOfModules.unit ((adicLisseForget W).obj (proEtaleConstantRing W B)))) := by
  let : Algebra (ULift.{u + 1} A) B := ULift.algebra' A B
  exact ⟨(@CategoryTheory.basisSheafIso.{u + 1, u, u + 1} W.ProEt inferInstance
    (ProEt.topology W) (integralCoefficientRingSheafify.{u, u} W)
    (inferInstance : (ProEt.topology W).HasSheafCompose
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}))
    (integralCoefficientAbSheafify.{u, u} W)
    (integralCoefficientAbLocallyBijective.{u, u} W)
    (CommRingCat.of (ULift.{u + 1} A)) (CommRingCat.of (ULift.{u + 1} B))
    inferInstance d (WeilConjectures.liftedBasis.{u, u} b)).symm⟩

private theorem finite_basis (W : Scheme.{u}) (e : ℕ)
    (he : PurCompactSupport.Ramification l E F i e) (hepos : 1 ≤ e) (n : ℕ) :
    ∃ d : ℕ, Nonempty ((∏ᶜ fun _ : Fin d ↦ SheafOfModules.unit
        ((adicLisseForget W).obj ((PurCompactSupport.finite l E (n + 1)
          (Nat.le_add_left 1 n)).ring W))) ≅
      (pbcRestrict ((PurCompactSupport.finiteChange l E F i e he hepos (n + 1)
        (Nat.le_add_left 1 n)).map W)).obj
          (SheafOfModules.unit ((adicLisseForget W).obj
            ((PurCompactSupport.finite l F (e * (n + 1))
              (Nat.mul_pos hepos (Nat.le_add_left 1 n))).ring W)))) := by
  let := i.toAlgebra
  let := (integralScalarIntegerInclusion l E F i).toAlgebra
  obtain ⟨b⟩ := WeilConjectures.integral_basis l E F i
  let I := Padic.coefficientExtensionIdeal l E (n + 1)
  let K := Padic.coefficientExtensionIdeal l F (e * (n + 1))
  have hK : K = I.map (algebraMap (Padic.coefficientExtensionIntegers l E)
      (Padic.coefficientExtensionIntegers l F)) := by
    have he' := he
    change Ideal.map (integralScalarIntegerInclusion l E F i)
      (Ideal.span {Padic.coefficientExtensionUniformizer l E} ^ 1) =
        Ideal.span {Padic.coefficientExtensionUniformizer l F} ^ e at he'
    simp only [pow_one] at he'
    change K = I.map (integralScalarIntegerInclusion l E F i)
    simp only [K, I, Padic.coefficientExtensionIdeal, Ideal.map_pow, he', pow_mul]
  have hle : I ≤ K.comap (algebraMap (Padic.coefficientExtensionIntegers l E)
      (Padic.coefficientExtensionIntegers l F)) := by
    rw [hK]
    exact Ideal.le_comap_map
  let := Ideal.Quotient.algebraQuotientOfLEComap hle
  obtain ⟨bq, -⟩ := CategoryTheory.adicQuotientBasis_exists (Module.finrank E F) b I K hK hle
  have hφ : algebraMap (Padic.coefficientExtensionRing l E (n + 1))
      (Padic.coefficientExtensionRing l F (e * (n + 1))) =
        PurCompactSupport.ramifiedMap l E F i e he (n + 1) := by
    ext x
    rfl
  refine ⟨Module.finrank E F, ?_⟩
  have hb := constant_basis W (Padic.coefficientExtensionRing l E (n + 1))
    (Padic.coefficientExtensionRing l F (e * (n + 1))) (Module.finrank E F) bq
  simp only [hφ] at hb
  unfold PurCompactSupport.finiteChange
  dsimp only [PurCompactSupport.finite, PurCompactSupport.ramifiedSheafMap]
  convert! hb using 1

private theorem proper_isIso_of_basis {R S : PurCompactSupport.Coefficients.{u}}
    (a : PurCompactSupport.Change R S) {Z W : Scheme.{u}} (g : Z ⟶ W) (d : ℕ)
    (bW : (∏ᶜ fun _ : Fin d ↦ SheafOfModules.unit ((adicLisseForget W).obj (R.ring W))) ≅
      (pbcRestrict (a.map W)).obj
        (SheafOfModules.unit ((adicLisseForget W).obj (S.ring W)))) :
    IsIso (PurCompactSupport.properComparison a g) := by
  have : (pbcRestrict (a.map W)).ReflectsIsomorphisms :=
    (proEtaleRingRestrictScalars_properties (a.map W)).2.2
  have : (pbcDerivedRestrict (a.map W)).ReflectsIsomorphisms :=
    exactDerived_reflectsIsomorphisms _
  have := (proEtaleRingDerivedAdjunction g (R.ring W) (R.ring Z) (R.pull g)).isRightAdjoint
  apply (NatTrans.isIso_iff_isIso_app _).2
  intro N
  let t := (proEtaleRingRestrictionDerivedDirectImage g
    (R.ring W) (S.ring W) (R.ring Z) (S.ring Z)
    (a.map W) (a.map Z) (R.pull g) (S.pull g) (a.square g)).hom.app
      ((pbcDerivedExtend (a.map Z)).obj N) ≫
    (proEtaleRingDerivedDirectImage g (R.ring W) (R.ring Z) (R.pull g)).map
      ((derivedCoordinates Z (a.map Z) d (pulledBasis a g d bW)).hom.app N) ≫
    piComparison (proEtaleRingDerivedDirectImage g (R.ring W) (R.ring Z) (R.pull g))
      (fun _ : Fin d ↦ N)
  have ht₁ := ((proEtaleRingRestrictionDerivedDirectImage g
    (R.ring W) (S.ring W) (R.ring Z) (S.ring Z)
    (a.map W) (a.map Z) (R.pull g) (S.pull g) (a.square g)).app
      ((pbcDerivedExtend (a.map Z)).obj N)).isIso_hom
  have ht₂ := ((proEtaleRingDerivedDirectImage g
    (R.ring W) (R.ring Z) (R.pull g)).mapIso
      ((derivedCoordinates Z (a.map Z) d (pulledBasis a g d bW)).app N)).isIso_hom
  have ht₃ := (PreservesProduct.iso
    (proEtaleRingDerivedDirectImage g (R.ring W) (R.ring Z) (R.pull g))
    (fun _ : Fin d ↦ N)).isIso_hom
  have ht : IsIso t := IsIso.comp_isIso' ht₁ (IsIso.comp_isIso' ht₂ ht₃)
  have hcomp : IsIso ((pbcDerivedRestrict (a.map W)).map
      ((PurCompactSupport.properComparison a g).app N) ≫ t) := by
    change IsIso (_ ≫ _ ≫ _ ≫ _)
    rw [proper_biproduct a g d bW N]
    exact ((derivedCoordinates W (a.map W) d bW).app
      ((proEtaleRingDerivedDirectImage g (R.ring W) (R.ring Z) (R.pull g)).obj N)).isIso_hom
  have hm : IsIso ((pbcDerivedRestrict (a.map W)).map
      ((PurCompactSupport.properComparison a g).app N)) :=
    @IsIso.of_isIso_comp_right _ _ _ _ _ _ t ht hcomp
  exact (isIso_iff_of_reflects_iso _ (pbcDerivedRestrict (a.map W))).mp hm

private theorem strictProper_isIso_of_basis {Z W : Scheme.{u}} (g : Z ⟶ W) (d : ℕ)
    (bW : (∏ᶜ fun _ : Fin d ↦
        SheafOfModules.unit ((adicLisseForget W).obj ((constants l E).ring W))) ≅
      (pbcRestrict (constantMap l E F i W)).obj
        (SheafOfModules.unit ((adicLisseForget W).obj ((constants l F).ring W)))) :
    IsIso (proper l E F i g) := by
  have : (pbcRestrict (constantMap l E F i W)).ReflectsIsomorphisms :=
    (proEtaleRingRestrictScalars_properties (constantMap l E F i W)).2.2
  have : (restrict l E F i W).ReflectsIsomorphisms := inferInstance
  have : (U l E F i W).ReflectsIsomorphisms := exactDerived_reflectsIsomorphisms _
  have := (AlgebraicGeometry.ProEtale.StrictTower.adj
    (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) g).isRightAdjoint
  apply (NatTrans.isIso_iff_isIso_app _).2
  intro N
  let t := (properRestriction l E F i g).hom.app ((T l E F i Z).obj N) ≫
    (R (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) g).map
      ((derivedTowerCoordinates Z (constantMap l E F i Z) d
        (pulledBasis (change l E F i) g d bW)).hom.app N) ≫
    piComparison (R (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) g)
      (fun _ : Fin d ↦ N)
  have ht₁ := ((properRestriction l E F i g).app ((T l E F i Z).obj N)).isIso_hom
  have ht₂ := ((R (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) g).mapIso
    ((derivedTowerCoordinates Z (constantMap l E F i Z) d
      (pulledBasis (change l E F i) g d bW)).app N)).isIso_hom
  have ht₃ := (PreservesProduct.iso
    (R (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) g)
    (fun _ : Fin d ↦ N)).isIso_hom
  have ht : IsIso t := IsIso.comp_isIso' ht₁ (IsIso.comp_isIso' ht₂ ht₃)
  have hcomp : IsIso ((U l E F i W).map ((proper l E F i g).app N) ≫ t) := by
    change IsIso (_ ≫ _ ≫ _ ≫ _)
    rw [strictProper_biproduct l E F i g d bW N]
    exact ((derivedTowerCoordinates W (constantMap l E F i W) d bW).app
      ((R (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) g).obj N)).isIso_hom
  have hm : IsIso ((U l E F i W).map ((proper l E F i g).app N)) :=
    @IsIso.of_isIso_comp_right _ _ _ _ _ _ t ht hcomp
  exact (isIso_iff_of_reflects_iso _ (U l E F i W)).mp hm

/-- The proper and open strict mates, and their finite quotient versions, are
isomorphisms. The finite proper assertion includes every derived input.
Source: Stacks 0B56, 0944, 0E8I
(blueprint: lem-pur-compact-support-strict-scalar-mate).
Proof: restriction of the proper map is the finite-biproduct comparison under
coordinates for one finite integral basis. Its columns are direct image of the
basis inclusions, by the adjunction counit and triangle identity. Additivity gives
its inverse. Restriction detects acyclic cones. The open map is ordinary balancing
on the open, and zero off it. The identical argument applies to all finite quotients. -/
theorem factors_isIso {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (e : ℕ) (he : PurCompactSupport.Ramification l E F i e) (hepos : 1 ≤ e) :
    IsIso (proper l E F i c.g) ∧ IsIso (openTensor l E F i c.i) ∧
      ∀ n : ℕ,
        IsIso (PurCompactSupport.properComparison
          (PurCompactSupport.finiteChange l E F i e he hepos (n + 1)
            (Nat.le_add_left 1 n)) c.g) ∧
          IsIso (PurCompactSupport.openComparison
            (PurCompactSupport.finiteChange l E F i e he hepos (n + 1)
              (Nat.le_add_left 1 n)) c.i) := by
  let := i.toAlgebra
  let := (integralScalarIntegerInclusion l E F i).toAlgebra
  obtain ⟨b⟩ := WeilConjectures.integral_basis l E F i
  obtain ⟨bY⟩ := constant_basis Y (Padic.coefficientExtensionIntegers l E)
    (Padic.coefficientExtensionIntegers l F) (Module.finrank E F) b
  refine ⟨strictProper_isIso_of_basis l E F i c.g (Module.finrank E F) bY, ?_, ?_⟩
  · rw [openTensor_ordinary l E F i c.i]
    exact (Functor.mapDerivedCategorySquareIso
      (@asIso _ _ _ _ (ordinaryOpenTensor l E F i c.i)
        (ordinaryOpenTensor_isIso l E F i c.i))).isIso_hom
  · intro n
    obtain ⟨d, ⟨bW⟩⟩ := finite_basis l E F i Y e he hepos n
    refine ⟨proper_isIso_of_basis _ c.g d bW, ?_⟩
    rw [open_base_ordinary _ c.i d
      (pulledBasis _ c.g d bW)]
    infer_instance

end MateInvertibility

/-- The finite proper arrow is exactly the geometric adjunction mate required in
the node, with canonical scalar/pullback balancing and the actual proper counit.
Source: Stacks 07A6, 0B56 (blueprint: lem-pur-compact-support-strict-scalar-mate).
Proof: expand scalarPull as the left-adjoint comparison conjugate to restriction
of proper image. The scalar and geometric adjunction triangles identify the
scalar mate with the displayed geometric transpose. This uses the normalized
composite adjunctions, so it fixes the arrow rather than just its endpoints. -/
theorem proper_geometric_transpose {R S : PurCompactSupport.Coefficients.{u}}
    (a : PurCompactSupport.Change R S) {Z W : Scheme.{u}} (g : Z ⟶ W)
    (N : DerivedCategory (pbcModules Z (R.ring Z))) :
    ((proEtaleRingDerivedAdjunction g (S.ring W) (S.ring Z) (S.pull g)).homEquiv _ _).symm
        ((PurCompactSupport.properComparison a g).app N) =
      (PurCompactSupport.scalarPull a g).inv.app
          ((proEtaleRingDerivedDirectImage g (R.ring W) (R.ring Z) (R.pull g)).obj N) ≫
        (pbcDerivedExtend (a.map Z)).map
          ((proEtaleRingDerivedAdjunction g (R.ring W) (R.ring Z) (R.pull g)).counit.app N) := by
  rw [PurCompactSupport.scalarPull, leftAdjointUniq_ofNatIsoRight_inv]
  exact scalarMate_geometric_transpose
    (proEtaleRingDerivedAdjunction g (R.ring W) (R.ring Z) (R.pull g))
    (pbcDerivedScalarAdjunction (a.map Z)) (pbcDerivedScalarAdjunction (a.map W))
    (proEtaleRingDerivedAdjunction g (S.ring W) (S.ring Z) (S.pull g))
    (proEtaleRingRestrictionDerivedDirectImage g
      (R.ring W) (S.ring W) (R.ring Z) (S.ring Z)
      (a.map W) (a.map Z) (R.pull g) (S.pull g) (a.square g)).symm N


set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The full compact-support scalar mate conclusion, kept as one transparent proposition.
This is the original conjunction, including the precise finite arrow and transition
normalizations; the abbreviation introduces no assertion or choice of data.
Source: Stacks 07A6, 0B56, 0940 and 0E8I; comparison Steps 3--4.
(blueprint: lem-pur-compact-support-strict-scalar-mate). -/
abbrev compactSupportStrictScalarMateConclusion
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (S : CoefficientDerivedSystemCalculus.{u, u} l E X)
    (S' : CoefficientDerivedSystemCalculus.{u, u} l F X) (e : ℕ)
    (he : PurCompactSupport.Ramification l E F i e) (hepos : 1 ≤ e) : Prop :=
    IsIso (Functor.whiskerLeft (finiteTorConstructibleIntegral l E X).ι
      (arrow l E F i c S S' e he hepos)) ∧
    ∀ (M : DerivedCategory (scalarReductionSource l E X))
      (_hM : finiteTorConstructibleIntegral l E X M),
      (∀ n : ℕ,
        (ev (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) Y n).map
            ((arrow l E F i c S S' e he hepos).app M) ≫
            (targetEvaluation l E F i c S' e he hepos n).hom.app M =
          (sourceEvaluation l E F i c S e he hepos n).hom.app M ≫
            (positiveRestriction l F Y (e * (n + 1))
              (Nat.mul_pos hepos (Nat.le_add_left 1 n))).map
              (PurCompactSupport.finiteTensorMap l E F i e he hepos n c M)) ∧
      (∀ n : ℕ, IsIso (PurCompactSupport.finiteTensorMap l E F i e he hepos n c M)) ∧
      ∀ (a b : ℕ) (hab : a ≤ b),
        (ev (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) Y b).map
            ((arrow l E F i c S S' e he hepos).app M) ≫
            (pbcTowerTransition Y ((constants l F).ring Y) b a hab).app
              ((support l F c S' ⋙ subsequence l F Y e).obj
                ((pbcDerivedExtend (completedCoefficientMap l E F i X)).obj M)) =
          (pbcTowerTransition Y ((constants l F).ring Y) b a hab).app
              ((support l E c S ⋙ T l E F i Y).obj M) ≫
            (ev (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) Y a).map
              ((arrow l E F i c S S' e he hepos).app M)

section FiniteField
variable (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  {X Y : Scheme.{u}}
  [Xbase : X.Over (Spec (.of D.k))] [Ybase : Y.Over (Spec (.of D.k))]
  [Xft : LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [Xqc : QuasiCompact (X ↘ Spec (.of D.k))] [Xs : IsSeparated (X ↘ Spec (.of D.k))]
  [Yft : LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
  [Yqc : QuasiCompact (Y ↘ Spec (.of D.k))] [Ys : IsSeparated (Y ↘ Spec (.of D.k))]
  (f : X ⟶ Y) [fbase : f.IsOver (Spec (.of D.k))]
  [fs : IsSeparated f] [fft : LocallyOfFiniteType f] [fqc : QuasiCompact f]
include D hl Xbase Ybase Xft Xqc Xs Yft Yqc Ys fbase fs fft fqc

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
set_option linter.unusedSectionVars false in
/-- The canonical B-linear map of derived strict support towers is invertible on
the stated derived-complete bounded constructible uniform finite-Tor domain.
Its evaluated arrow is the specified finite proper mate followed by proper image
of the open tensor map. Quotient squares commute before any derived limit.
Source: Stacks 07A6, 0B56, 0940 and 0E8I; extracted comparison Steps 3--4
(blueprint: lem-pur-compact-support-strict-scalar-mate).
Proof: restrict native separately derived support to constant integral towers by
the normalized proper/open comparisons. Apply the strict scalar proper mate and
open tensor balancing, then the whole-complex ramified reduction balancing and
exact arithmetic selection. A finite integral basis identifies restricted proper
mates with finite-biproduct comparisons; open balancing is already an isomorphism.
Thus the entire natural transformation is invertible. The normalized evaluation
counits give precisely the finite proper transpose and open-unit map. Tensor
balancing gives the source/target identifications displayed here. Naturality of
strict-tower transitions proves their commuting squares. All constructions precede
inverse limits and use no choice of basis; scalar mate pasting gives the final
normalization recorded in comparison_pasted. -/
theorem compactSupportStrictScalarMate (c : Compactification f)
    (S : CoefficientDerivedSystemCalculus.{u, u} l E X)
    (S' : CoefficientDerivedSystemCalculus.{u, u} l F X) (e : ℕ)
    (he : PurCompactSupport.Ramification l E F i e) (hepos : 1 ≤ e) :
    compactSupportStrictScalarMateConclusion l E F i c S S' e he hepos := by
  obtain ⟨hp, hj, hfinite⟩ := factors_isIso l E F i c e he hepos
  have hproper : IsIso (proper l E F i c.g) := hp
  have hopen : IsIso (openTensor l E F i c.i) := hj
  have hleft : IsIso (Functor.whiskerLeft
      (J (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) c.i)
      (proper l E F i c.g)) := inferInstance
  have hright : IsIso (Functor.whiskerRight (openTensor l E F i c.i)
      (R (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) c.g)) := inferInstance
  have hcomparison : IsIso (comparison l E F i c) := by
    unfold comparison
    exact IsIso.comp_isIso' hleft hright
  have := hcomparison
  have harrow : IsIso (arrow l E F i c S S' e he hepos) := by
    unfold arrow
    infer_instance
  have := harrow
  refine ⟨inferInstance, ?_⟩
  intro M _hM
  refine ⟨strictScalarMate_finiteEvaluation l E F i c S S' e he hepos M, ?_, ?_⟩
  · intro n
    obtain ⟨hpfin, hjfin⟩ := hfinite n
    let a := PurCompactSupport.finiteChange l E F i e he hepos (n + 1)
      (Nat.le_add_left 1 n)
    let N := (pbcDerivedExtend (PurCompactSupport.projection l E (n + 1)
      (Nat.le_add_left 1 n) X)).obj M
    have hpN := ((@asIso _ _ _ _ (PurCompactSupport.properComparison a c.g) hpfin).app
      ((PurCompactSupport.openExtension (PurCompactSupport.finite l E (n + 1)
        (Nat.le_add_left 1 n)) c.i).mapDerivedCategory.obj N)).isIso_hom
    have hjN := ((proEtaleRingDerivedDirectImage c.g
      ((PurCompactSupport.finite l F (e * (n + 1))
        (Nat.mul_pos hepos (Nat.le_add_left 1 n))).ring Y)
      ((PurCompactSupport.finite l F (e * (n + 1))
        (Nat.mul_pos hepos (Nat.le_add_left 1 n))).ring c.Z)
      ((PurCompactSupport.finite l F (e * (n + 1))
        (Nat.mul_pos hepos (Nat.le_add_left 1 n))).pull c.g)).mapIso
      ((@asIso _ _ _ _ (PurCompactSupport.openComparison a c.i) hjfin).app N)).isIso_hom
    exact IsIso.comp_isIso' hpN hjN
  · intro a b hab
    exact (pbcTowerTransition Y ((constants l F).ring Y) b a hab).naturality
      ((arrow l E F i c S S' e he hepos).app M)
end FiniteField

end WeilConjectures.PurStrictScalar
