/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SfRationalizationKaroubi
public import WeilConjectures.AlgebraicGeometry.GeneralAlgebraicallyClosedCoefficients
public import WeilConjectures.AlgebraicGeometry.DerivedPullbackTensorHom
public import WeilConjectures.AlgebraicGeometry.SfDerivedDirectImage
public import WeilConjectures.AlgebraicGeometry.QcqsCompactSupportRealization
public import WeilConjectures.AlgebraicGeometry.CompactSupportCoefficientAction
public import WeilConjectures.AlgebraicGeometry.SfRationalLocalizationOrthogonality
public import WeilConjectures.AlgebraicGeometry.FiniteFieldFiberSupplement
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Shift.Adjunction
public import Mathlib.CategoryTheory.Triangulated.Functor

/-! # Finite coherent localization data

Source: the algebraically closed-stage localization argument, coefficient
comparison and adjunction compatibility steps.
(blueprint: lem-sf-qbar-localization-finite-coherence).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOf false
set_option genCtorIdx false
set_option genSizeOfSpec false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u v
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry
namespace WeilConjectures
attribute [local irreducible] sfIntegralConstructible FrobeniusExchange.models
  sfRationalTriangulationDatum
open GeneralAlgebraicallyClosedCoefficients
open AlgebraicallyClosedCoefficients (Index Coefficient)
variable (l : ℕ) [Fact l.Prime]
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

/-- Finite exact structures and their scalar coherence, before descent.
Source: algebraically closed-stage localization proof, steps 1--2.
(blueprint: def-sf-qbar-localization-finite-data). -/
structure SfLocalizationFiniteExact {V W : Scheme.{u}}
    (system : (stageSystem l Ω V).Morphism (stageSystem l Ω W)) where
  shift : ∀ E, (system.Φ E).CommShift ℤ
  additive : ∀ E, (system.Φ E).Additive
  exact : ∀ E, letI := shift E; (system.Φ E).IsTriangulated
  beta_shift : ∀ {E L : Index l Ω} (h : E ≤ L),
    letI := shift E
    letI := shift L
    NatTrans.CommShift (system.β h).hom ℤ
  unit : ∀ (E : Index l Ω) (K : Stage l Ω V E),
    (system.β (le_refl E)).hom.app K ≫
        (system.Φ E).map ((operationStageTransitionIso l Ω V E E le_rfl).hom.app K ≫
          (unitor l Ω V E).hom.app K) =
      (operationStageTransitionIso l Ω W E E le_rfl).hom.app ((system.Φ E).obj K) ≫
        (unitor l Ω W E).hom.app ((system.Φ E).obj K)

section Descent
variable (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  {X Z U : Scheme.{u}}
  [X.Over (Spec (.of D.k))] [Z.Over (Spec (.of D.k))] [U.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [IsSeparated (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Z ↘ Spec (.of D.k))] [QuasiCompact (Z ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (U ↘ Spec (.of D.k))] [QuasiCompact (U ↘ Spec (.of D.k))]
  (i : Z ⟶ X) (j : U ⟶ X) [i.IsOver (Spec (.of D.k))] [j.IsOver (Spec (.of D.k))]
  [IsClosedImmersion i] [IsOpenImmersion j] [QuasiCompact j]
  [∀ x : X, Invertible (l : X.residueField x)]
  [∀ z : Z, Invertible (l : Z.residueField z)]
  [∀ t : U, Invertible (l : U.residueField t)]

/-- The four normalized finite functor families and compatible adjunction maps.
No common-stage adjunction, exactness, triangle or Hom comparison is asserted here.
Source: localization proof, coefficient compatibility and finite-stage normalization.
(blueprint: def-sf-qbar-localization-finite-data). -/
structure SfQbarLocalizationFiniteData where
  finiteLocalization : ∀ E : Index l Ω,
    SfRationalLocalizationOrthogonality l (Coefficient.{u} l Ω E) D i j
  openAction : SfCompactSupportCoefficientAction l D.k
    (PurCompactSupport.coefficientPrimeUnit l D hl) Ω (Compactification.ofIsOpenImmersion j)
  closedAction : (stageSystem l Ω Z).Morphism (stageSystem l Ω X)
  closedAction_finite : ∀ E, closedAction.Φ E =
    (finiteLocalization E).closedRationalImage
  openPull : (stageSystem l Ω X).Morphism (stageSystem l Ω U)
  closedPull : (stageSystem l Ω X).Morphism (stageSystem l Ω Z)
  openPull_finite : ∀ E, openPull.Φ E = rationalDerivedPullback l (Coefficient.{u} l Ω E) j
  closedPull_finite : ∀ E, closedPull.Φ E = rationalDerivedPullback l (Coefficient.{u} l Ω E) i
  openPull_beta : ∀ (E L : Index l Ω) (h : E ≤ L) (K : Stage l Ω X E),
    HEq ((openPull.β h).app K) (commonStagePullbackComparison l Ω j ⟨E, K⟩ L h)
  closedPull_beta : ∀ (E L : Index l Ω) (h : E ≤ L) (K : Stage l Ω X E),
    HEq ((closedPull.β h).app K) (commonStagePullbackComparison l Ω i ⟨E, K⟩ L h)
  openExact : SfLocalizationFiniteExact l Ω openAction.system
  closedExact : SfLocalizationFiniteExact l Ω closedAction
  openPullExact : SfLocalizationFiniteExact l Ω openPull
  closedPullExact : SfLocalizationFiniteExact l Ω closedPull
  finiteOpenAdjunction : ∀ E, openAction.system.Φ E ⊣ openPull.Φ E
  finiteClosedAdjunction : ∀ E, closedPull.Φ E ⊣ closedAction.Φ E
  finiteOpenAdjunction_normalization : ∀ E,
    HEq (finiteOpenAdjunction E) (finiteLocalization E).openRationalAdjunction
  finiteClosedAdjunction_normalization : ∀ E,
    HEq (finiteClosedAdjunction E) (finiteLocalization E).closedRationalAdjunction
  closedAction_beta : ∀ (E L : Index l Ω) (h : E ≤ L),
    (closedAction.β h).hom =
      (mateEquiv (finiteClosedAdjunction E) (finiteClosedAdjunction L)
        (TwoSquare.mk _ _ _ _ (closedPull.β h).inv)).natTrans
  openShift_finite : ∀ E,
    HEq (openExact.shift E) (finiteLocalization E).openPush.rationalShift
  closedShift_finite : ∀ E,
    HEq (closedExact.shift E) (finiteLocalization E).closedPush.rationalShift
  openPullShift_finite : ∀ E,
    HEq (openPullExact.shift E) (finiteLocalization E).openPull.rationalShift
  closedPullShift_finite : ∀ E,
    HEq (closedPullExact.shift E) (finiteLocalization E).closedPull.rationalShift
  finiteOpenAdjunction_shift : ∀ E,
    letI := openExact.shift E
    letI := openPullExact.shift E
    (finiteOpenAdjunction E).CommShift ℤ
  finiteClosedAdjunction_shift : ∀ E,
    letI := closedPullExact.shift E
    letI := closedExact.shift E
    (finiteClosedAdjunction E).CommShift ℤ
  openUnit : StageSystem.Morphism.Hom (StageSystem.Morphism.id (stageSystem l Ω U))
    (openAction.system.comp openPull)
  openCounit : StageSystem.Morphism.Hom (openPull.comp openAction.system)
    (StageSystem.Morphism.id (stageSystem l Ω X))
  closedUnit : StageSystem.Morphism.Hom (StageSystem.Morphism.id (stageSystem l Ω X))
    (closedPull.comp closedAction)
  closedCounit : StageSystem.Morphism.Hom (closedAction.comp closedPull)
    (StageSystem.Morphism.id (stageSystem l Ω Z))
  openUnit_finite : ∀ E, openUnit.τ E = (finiteOpenAdjunction E).unit
  openCounit_finite : ∀ E, openCounit.τ E = (finiteOpenAdjunction E).counit
  closedUnit_finite : ∀ E, closedUnit.τ E = (finiteClosedAdjunction E).unit
  closedCounit_finite : ∀ E, closedCounit.τ E = (finiteClosedAdjunction E).counit

end Descent
end WeilConjectures
