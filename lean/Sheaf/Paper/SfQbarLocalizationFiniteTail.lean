/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.SfQbarLocalizationFiniteBase

/-! # Coherence fields for finite normalized localization

Source: the finite-stage localization argument, steps 3--5.
(blueprint: lem-sf-qbar-localization-finite-coherence).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures
open GeneralAlgebraicallyClosedCoefficients
open AlgebraicallyClosedCoefficients (Index Coefficient)
variable (l : ℕ) [Fact l.Prime]
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

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

/-- The exact, adjunction, shift, and unit/counit coherence fields after the
finite operation data have been fixed.
Source: finite-stage localization proof, steps 3--5
(blueprint: lem-sf-qbar-localization-finite-coherence). -/
structure SfQbarLocalizationFiniteTail
    (B : SfQbarLocalizationFiniteBase l Ω D hl i j) where
  openExact : SfLocalizationFiniteExact l Ω B.openAction.system
  closedExact : SfLocalizationFiniteExact l Ω B.closedAction
  openPullExact : SfLocalizationFiniteExact l Ω B.openPull
  closedPullExact : SfLocalizationFiniteExact l Ω B.closedPull
  finiteOpenAdjunction : ∀ E, B.openAction.system.Φ E ⊣ B.openPull.Φ E
  finiteClosedAdjunction : ∀ E, B.closedPull.Φ E ⊣ B.closedAction.Φ E
  finiteOpenAdjunction_normalization : ∀ E,
    HEq (finiteOpenAdjunction E) (B.finiteLocalization E).openRationalAdjunction
  finiteClosedAdjunction_normalization : ∀ E,
    HEq (finiteClosedAdjunction E) (B.finiteLocalization E).closedRationalAdjunction
  closedAction_beta : ∀ (E L : Index l Ω) (h : E ≤ L),
    (B.closedAction.β h).hom =
      (mateEquiv (finiteClosedAdjunction E) (finiteClosedAdjunction L)
        (TwoSquare.mk _ _ _ _ (B.closedPull.β h).inv)).natTrans
  openShift_finite : ∀ E,
    HEq (openExact.shift E) (B.finiteLocalization E).openPush.rationalShift
  closedShift_finite : ∀ E,
    HEq (closedExact.shift E) (B.finiteLocalization E).closedPush.rationalShift
  openPullShift_finite : ∀ E,
    HEq (openPullExact.shift E) (B.finiteLocalization E).openPull.rationalShift
  closedPullShift_finite : ∀ E,
    HEq (closedPullExact.shift E) (B.finiteLocalization E).closedPull.rationalShift
  finiteOpenAdjunction_shift : ∀ E,
    letI := openExact.shift E
    letI := openPullExact.shift E
    (finiteOpenAdjunction E).CommShift ℤ
  finiteClosedAdjunction_shift : ∀ E,
    letI := closedPullExact.shift E
    letI := closedExact.shift E
    (finiteClosedAdjunction E).CommShift ℤ
  openUnit : StageSystem.Morphism.Hom (StageSystem.Morphism.id (stageSystem l Ω U))
    (B.openAction.system.comp B.openPull)
  openCounit : StageSystem.Morphism.Hom (B.openPull.comp B.openAction.system)
    (StageSystem.Morphism.id (stageSystem l Ω X))
  closedUnit : StageSystem.Morphism.Hom (StageSystem.Morphism.id (stageSystem l Ω X))
    (B.closedPull.comp B.closedAction)
  closedCounit : StageSystem.Morphism.Hom (B.closedAction.comp B.closedPull)
    (StageSystem.Morphism.id (stageSystem l Ω Z))
  openUnit_finite : ∀ E, openUnit.τ E = (finiteOpenAdjunction E).unit
  openCounit_finite : ∀ E, openCounit.τ E = (finiteOpenAdjunction E).counit
  closedUnit_finite : ∀ E, closedUnit.τ E = (finiteClosedAdjunction E).unit
  closedCounit_finite : ∀ E, closedCounit.τ E = (finiteClosedAdjunction E).counit

/-- Existence of all coherence fields for a fixed finite operation package.
Source: finite-stage localization proof, steps 3--5
(blueprint: lem-sf-qbar-localization-finite-coherence). -/
theorem sfQbarLocalizationFiniteTail_exists
    (hij : Set.range i.base = (Set.range j.base)ᶜ)
    (B : SfQbarLocalizationFiniteBase l Ω D hl i j) :
    Nonempty (SfQbarLocalizationFiniteTail l Ω D hl i j B) := by
  sorry

end Descent
end WeilConjectures
