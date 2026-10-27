/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.SfQbarLocalizationFiniteData

/-! # Finite operation data for normalized localization

Source: the finite-stage localization argument, steps 1--2.
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

/-- The finite localization operations and their prescribed stage comparisons.
Source: finite-stage localization proof, steps 1--2
(blueprint: lem-sf-qbar-localization-finite-coherence). -/
structure SfQbarLocalizationFiniteBase where
  finiteLocalization : ∀ E : Index l Ω,
    SfRationalLocalizationOrthogonality l (Coefficient.{u} l Ω E) D i j
  openAction : SfCompactSupportCoefficientAction l D.k
    (PurCompactSupport.coefficientPrimeUnit l D hl) Ω (Compactification.ofIsOpenImmersion j)
  closedAction : (stageSystem l Ω Z).Morphism (stageSystem l Ω X)
  closedAction_finite : ∀ E, closedAction.Φ E =
    (finiteLocalization E).closedRationalImage
  openPull : (stageSystem l Ω X).Morphism (stageSystem l Ω U)
  closedPull : (stageSystem l Ω X).Morphism (stageSystem l Ω Z)
  openPull_finite : ∀ E, openPull.Φ E =
    rationalDerivedPullback l (Coefficient.{u} l Ω E) j
  closedPull_finite : ∀ E, closedPull.Φ E =
    rationalDerivedPullback l (Coefficient.{u} l Ω E) i
  openPull_beta : ∀ (E L : Index l Ω) (h : E ≤ L) (K : Stage l Ω X E),
    HEq ((openPull.β h).app K) (commonStagePullbackComparison l Ω j ⟨E, K⟩ L h)
  closedPull_beta : ∀ (E L : Index l Ω) (h : E ≤ L) (K : Stage l Ω X E),
    HEq ((closedPull.β h).app K) (commonStagePullbackComparison l Ω i ⟨E, K⟩ L h)

/-- Existence of the operation part of the finite localization package.
Source: finite-stage localization proof, steps 1--2
(blueprint: lem-sf-qbar-localization-finite-coherence). -/
theorem sfQbarLocalizationFiniteBase_exists
    (hij : Set.range i.base = (Set.range j.base)ᶜ) :
    Nonempty (SfQbarLocalizationFiniteBase l Ω D hl i j) := by
  sorry

end Descent
end WeilConjectures
