/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Sf.SfQbarLocalizationFiniteData
import WeilConjectures.SmoothPurity.Compact.CompactSupportFiniteFieldIndependence
import WeilConjectures.SmoothPurity.Sf.SfRationalDirectImageCoefficientCompatibility
import all WeilConjectures.SmoothPurity.Sf.SfCommonStageDirectImage

/-! # Finite operation data for normalized localization

Source: the finite-stage localization argument, steps 1--2.
(blueprint: lem-sf-qbar-localization-finite-coherence).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
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
  classical
  have hji : Set.range j.base = (Set.range i.base)ᶜ := by
    rw [hij, compl_compl]
  have hfinite (E : Index l Ω) :=
    sfRationalLocalizationTriangleOrthogonality l (Coefficient.{u} l Ω E) D hl i j hji
  let H : ∀ E : Index l Ω, SfRationalLocalizationOrthogonality l (Coefficient.{u} l Ω E) D i j :=
    fun E ↦ Classical.choice (hfinite E)
  obtain ⟨A, _⟩ := sfCompactSupportFiniteFieldIndependence l D.k
    (PurCompactSupport.coefficientPrimeUnit l D hl) Ω (Compactification.ofIsOpenImmersion j)
  obtain ⟨P, ⟨hP, hPβ, _⟩, _⟩ :=
    sfRationalDirectImageCoefficientCompatibility l Ω j
  obtain ⟨Q, ⟨hQ, hQβ, hm⟩, _⟩ :=
    sfRationalDirectImageCoefficientCompatibility l Ω i
  let R E := (H E).closedRationalImage
  let a E : Q.Φ E ⊣ R E :=
    ((H E).closedRationalAdjunction).ofNatIsoLeft (eqToIso (congrFun hQ E)).symm
  let b {E F : Index l Ω} (h : E ≤ F) :
      R E ⋙ (stageSystem l Ω X).T h ≅ (stageSystem l Ω Z).T h ⋙ R F := by
    let := hm R a h
    exact asIso ((mateEquiv (a E) (a F) (TwoSquare.mk _ _ _ _ (Q.β h).inv)).natTrans)
  have hb {E F : Index l Ω} (h : E ≤ F) (K : Stage l Ω Z E) :
      (Q.Φ F).map ((b h).hom.app K) ≫
          (a F).counit.app (((stageSystem l Ω Z).T h).obj K) =
        (Q.β h).inv.app ((R E).obj K) ≫
          ((stageSystem l Ω Z).T h).map ((a E).counit.app K) :=
    mateEquiv_counit (a E) (a F) (TwoSquare.mk _ _ _ _ (Q.β h).inv) K
  exact ⟨{
    finiteLocalization := H
    openAction := A
    closedAction := DirectImageAdjunction.mateFamily Q R a b hb
    closedAction_finite := fun _ ↦ rfl
    openPull := P
    closedPull := Q
    openPull_finite := congrFun hP
    closedPull_finite := congrFun hQ
    openPull_beta := hPβ
    closedPull_beta := hQβ }⟩

end Descent
end WeilConjectures
