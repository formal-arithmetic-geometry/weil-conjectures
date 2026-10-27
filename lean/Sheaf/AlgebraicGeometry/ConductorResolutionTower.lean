/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W9
-/
module

public import Sheaf.AlgebraicGeometry.ConductorResolutionPreparation
import Sheaf.AlgebraicGeometry.NormalizedBlowupCalculus
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Explicit conductor-prepended towers

Source: ILO VIII 2.2.3--2.2.5 and 2.3.2--2.3.4.
(blueprint: lem-trf-conductor-resolution-tower).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

open Monoscheme

/-- The conductor is finitely generated on every affine input chart.
Source: Stacks 01T6 and Noetherianity of affine rings.
(blueprint: lem-trf-conductor-resolution-tower). -/
theorem rationalConductor_finiteGeneration (X : RationalResolutionInput.{u})
    (U : X.scheme.affineOpens) : ((conductorIdeal X.scheme).ideal U).FG := by
  have := X.finiteType
  have := X.quasiCompact
  have : IsLocallyNoetherian X.scheme :=
    LocallyOfFiniteType.isLocallyNoetherian X.structureMap
  have := IsLocallyNoetherian.component_noetherian U
  exact IsNoetherian.noetherian _

/-- A unit conductor has an isomorphism as its normalized blowup map.
Source: ILO VIII 2.2.3--2.2.4.
(blueprint: lem-trf-conductor-resolution-tower). -/
theorem rationalConductor_unit_isIso (X : RationalResolutionInput.{u})
    (h : conductorIdeal X.scheme = ⊤) :
    IsIso (conductorIdeal X.scheme).normalizedBlowupMap := by
  have := X.reduced
  have := X.finiteType
  have := X.quasiCompact
  have hd := (rationalConductor_geometry X).nowhereDense
  have hdense : Dense ((conductorIdeal X.scheme).support.compl : Set X.scheme) :=
    interior_eq_empty_iff_dense_compl.mp
      ((conductorIdeal X.scheme).support.isClosed.isNowhereDense_iff.mp hd)
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hu, _⟩ :=
    Scheme.IdealSheafData.normalizedBlowup_calculus X.scheme X.structureMap
      (conductorIdeal X.scheme) (rationalConductor_finiteGeneration X) hdense
  have hn := (rationalConductor_geometry X).unit_iff.mp h
  rw [h]
  exact (hu hn).2

/-- Prepend the actual conductor arrow to the supplied tail, retaining its level zero
through the supplied base isomorphism. Source: ILO VIII 2.2.3--2.2.5.
(blueprint: lem-trf-conductor-resolution-tower). -/
noncomputable def conductorPrependedTower (X : RationalResolutionInput.{u})
    (A : QENormalizedResolutionTower (conductorPreparedRationalInput X).scheme) :
    NormalizedTower (A.length + 1) where
  level := Fin.cases X.scheme A.tower.level
  reduced := Fin.cases X.reduced A.tower.reduced
  center := Fin.cases (conductorIdeal X.scheme) A.tower.center
  arrow := Fin.cases (A.initial.hom ≫ (conductorIdeal X.scheme).normalizedBlowupMap)
    A.tower.arrow
  blowup := Fin.cases ⟨rationalConductor_finiteGeneration X, A.initial, rfl⟩ A.tower.blowup

/-- The actual conductor extension: rebase the given tower for unit conductor, and
prepend its normalized blowup otherwise. No tower data is selected from an existence
claim. Source: ILO VIII 2.2.3--2.2.5 and 2.3.2--2.3.4.
(blueprint: lem-trf-conductor-resolution-tower). -/
noncomputable def rationalConductorTower (X : RationalResolutionInput.{u})
    (A : QENormalizedResolutionTower (conductorPreparedRationalInput X).scheme) :
    QENormalizedResolutionTower X.scheme := by
  classical
  by_cases h : conductorIdeal X.scheme = ⊤
  · have := rationalConductor_unit_isIso X h
    exact { A with initial := A.initial ≪≫ asIso (conductorIdeal X.scheme).normalizedBlowupMap }
  · refine
      { length := A.length + 1
        tower := conductorPrependedTower X A
        initial := Iso.refl _
        coherent := Fin.cases (rationalConductor_geometry X).coherent A.coherent
        nonempty := Fin.cases ?_ A.nonempty
        nowhereDense := Fin.cases (rationalConductor_geometry X).nowhereDense A.nowhereDense
        regular := A.regular }
    by_contra hn
    apply h
    apply (Scheme.IdealSheafData.support_eq_bot_iff _).mp
    apply SetLike.coe_injective
    exact Set.not_nonempty_iff_eq_empty.mp hn

/-- All levels, arrows and centers of the explicit tower have the required conductor
shift; the unit branch has no added arrow. Source: ILO VIII 2.2.5 and 2.3.4.
(blueprint: lem-trf-conductor-resolution-tower).

Proof: in the unit branch use identity embeddings and level isomorphisms. In the
nonunit branch use successor embeddings and identity tail isomorphisms. The new
zero stage is the conductor by construction. All transport equations reduce to
identity morphisms and the given initial isomorphism of the tail. -/
theorem rationalConductorTower_extension (X : RationalResolutionInput.{u})
    (A : QENormalizedResolutionTower (conductorPreparedRationalInput X).scheme) :
    Nonempty (IsRationalConductorResolutionExtension X A (rationalConductorTower X A)) := by
  classical
  by_cases h : conductorIdeal X.scheme = ⊤
  · simp only [rationalConductorTower, dif_pos h]
    refine ⟨{
      levelIndex := OrderEmbedding.id _
      stageIndex := OrderEmbedding.id _
      length := by simp [rationalConductorStageCount, h]
      levelValue := by intro i; simp [rationalConductorStageCount, h]
      stageValue := by intro i; simp [rationalConductorStageCount, h]
      before := fun _ ↦ rfl
      after := fun _ ↦ rfl
      tailIso := fun _ ↦ Iso.refl _
      tailArrow := by intro i; simp
      tailCenter := by intro i; simp
      unitBase := by intro _; exact ⟨rfl, by simp⟩
      conductorStage := by intro hn; exact (hn h).elim }⟩
  · simp only [rationalConductorTower, dif_neg h]
    refine ⟨{
      levelIndex := Fin.succOrderEmb _
      stageIndex := Fin.succOrderEmb _
      length := by simp [rationalConductorStageCount, h]
      levelValue := by intro i; simp [rationalConductorStageCount, h]
      stageValue := by intro i; simp [rationalConductorStageCount, h]
      before := fun _ ↦ rfl
      after := fun _ ↦ rfl
      tailIso := fun _ ↦ Iso.refl _
      tailArrow := by intro i; simp [conductorPrependedTower]
      tailCenter := by intro i; simp [conductorPrependedTower]
      unitBase := by intro hu; exact (h hu).elim
      conductorStage := by intro _; exact ⟨0, rfl, rfl, by simp [conductorPrependedTower]⟩ }⟩

end AlgebraicGeometry
