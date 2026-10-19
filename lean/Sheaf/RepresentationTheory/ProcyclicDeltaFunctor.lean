/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF worker E6
-/
module

public import Sheaf.RepresentationTheory.ProcyclicComplex
public import Sheaf.CategoryTheory.DiscreteModulesAbelian
public import WeilConjectures.CategoryTheory.DeltaFunctor
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Homology.HomologySequenceLemmas
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.Algebra.Homology.HomologicalComplexAbelian

/-!
# Delta-functor of the two-term action complex

Source: blueprint lem-exc-procyclic-two-term, first paragraph; Stacks, Tag 0117.
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace Rep

private theorem complexDeltaFunctor
    {C D : Type*} [Category C] [Abelian C] [Category D] [Abelian D]
    (K : C ⥤ CochainComplex D ℕ) [K.Additive]
    (hex : ∀ (S : ShortComplex C), S.ShortExact → (S.map K).ShortExact)
    (hmono : ∀ (S : ShortComplex C), S.ShortExact → Mono ((K.map S.f).f 0)) :
    ∃ T : CohomologicalDeltaFunctor C D,
      T.F = fun q ↦ K ⋙ HomologicalComplex.homologyFunctor D (ComplexShape.up ℕ) q := by
  let T : CohomologicalDeltaFunctor C D :=
    { F := fun q ↦ K ⋙ HomologicalComplex.homologyFunctor D (ComplexShape.up ℕ) q
      additive := fun q ↦ inferInstance
      delta := fun S hS q ↦ (hex S hS).δ q (q + 1) rfl
      mono_zero := by
        intro S hS
        have := hmono S hS
        exact HomologicalComplex.mono_homologyMap_of_mono_of_not_rel (K.map S.f) 0
          (by intro i; simp)
      exact_middle := fun S hS q ↦ ⟨_, (hex S hS).homology_exact₂ q⟩
      exact_right := fun S hS q ↦ ⟨_, (hex S hS).homology_exact₃ q (q + 1) rfl⟩
      exact_left := fun S hS q ↦ ⟨_, (hex S hS).homology_exact₁ q (q + 1) rfl⟩
      naturality := fun S T hS hT φ q ↦
        HomologicalComplex.HomologySequence.δ_naturality
          (K.mapShortComplex.map φ) (hex S hS) (hex T hT) q (q + 1) rfl }
  exact ⟨T, rfl⟩

set_option linter.style.haveILetI false in
/-- The two-term action complex gives a cohomological delta-functor.

Proof: the forgetful functor preserves finite limits and colimits and detects exactness.
It is therefore additive, and its maps form a short exact sequence of modules whenever
the coefficient sequence is short exact. Evaluation of the two-term complex yields this
sequence in degrees zero and one and a zero sequence otherwise. Thus it preserves short
exact sequences. The homology long exact sequence gives the connecting maps and exactness;
its naturality gives the delta-functor naturality. The initial map is monic because no
nonzero differential enters degree zero.

Source: blueprint lem-exc-procyclic-two-term, first proof paragraph;
Stacks homology.tex, Tag 0117 (blueprint: lem-exc-procyclic-delta-functor). -/
theorem actionTwoTerm_deltaFunctor
    (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (A : Type u) [Ring A] [Finite A] (τ : G) :
    let h := Classical.choose (discreteModules_abelian.{v, u, w} G A)
    letI := h
    letI : Preadditive (DiscreteContinuousRep.{u, v, w} A G) := h.toPreadditive
    ∃ T : CohomologicalDeltaFunctor
        (DiscreteContinuousRep.{u, v, w} A G) (ModuleCat.{w} A),
      T.F = fun q ↦ actionTwoTerm A G τ ⋙
        HomologicalComplex.homologyFunctor (ModuleCat.{w} A) (ComplexShape.up ℕ) q := by
  classical
  dsimp only
  let h := Classical.choose (discreteModules_abelian.{v, u, w} G A)
  letI := h
  letI : Preadditive (DiscreteContinuousRep.{u, v, w} A G) := h.toPreadditive
  let U := ObjectProperty.ι (fun X : Rep.{w} A G ↦
    ∀ m : X.V, IsOpen {g : G | X.ρ g m = m}) ⋙
    forget₂ (Rep.{w} A G) (ModuleCat.{w} A)
  obtain ⟨hzero, hrest⟩ := Classical.choose_spec (discreteModules_abelian.{v, u, w} G A)
  letI : HasZeroMorphisms (DiscreteContinuousRep.{u, v, w} A G) :=
    Preadditive.preadditiveHasZeroMorphisms
  letI : U.PreservesZeroMorphisms := by
    convert hzero using 1
    exact Subsingleton.elim _ _
  have hu := hrest
  letI : PreservesFiniteLimits U := hu.2.1
  letI : PreservesFiniteColimits U := hu.2.2.1
  letI : U.Additive := Functor.additive_of_preserves_binary_products U
  let K := actionTwoTerm.{u, v, w} A G τ
  have hKadd : K.Additive := by
    constructor
    intro M N f g
    apply HomologicalComplex.Hom.ext
    funext n
    cases n with
    | zero => exact U.map_add
    | succ n =>
      cases n with
      | zero => exact U.map_add
      | succ n => simp [K, actionTwoTerm, actionTwoTermMap]
  letI := hKadd
  have hseq (S : ShortComplex (DiscreteContinuousRep.{u, v, w} A G))
      (hS : S.ShortExact) : (S.map K).ShortExact := by
    apply HomologicalComplex.shortExact_of_degreewise_shortExact
    intro n
    cases n with
    | zero =>
      have := hS.mono_f
      have := hS.epi_g
      exact hS.map U
    | succ n =>
      cases n with
      | zero =>
        have := hS.mono_f
        have := hS.epi_g
        exact hS.map U
      | succ n =>
        refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
        · apply ShortComplex.exact_of_isZero_X₂
          exact ModuleCat.isZero_iff_subsingleton.mpr (by
            change Subsingleton PUnit.{w + 1}
            infer_instance)
        · apply IsZero.mono
          exact actionTwoTerm_isZero A G τ S.X₁ (n + 1 + 1) (by omega)
        · apply IsZero.epi
          exact actionTwoTerm_isZero A G τ S.X₃ (n + 1 + 1) (by omega)
  apply complexDeltaFunctor K hseq
  intro S hS
  have := (hS.map_of_exact U).mono_f
  exact this

end Rep
