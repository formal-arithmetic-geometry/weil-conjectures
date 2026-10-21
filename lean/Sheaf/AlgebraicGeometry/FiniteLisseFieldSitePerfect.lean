/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A7
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Perfect.SitePerfect
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Mathlib.Data.ZMod.Basic

import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Field.ULift

import Sheaf.AlgebraicGeometry.FiniteRingDerivedLocalConstancy
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! # Local perfect models of bounded finite-lisse complexes

Source: blueprint lem-fin-lisse-field-dual, local-free calculation and finite truncation.
(blueprint: lem-fin-lisse-field-site-perfect).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale

/-- Bounded complexes with finite-lisse homology over a prime field are site-perfect.

Source: blueprint lem-fin-lisse-field-dual, local finite-free calculation; Stacks
Cohomology on Sites, Tag 094G (lemma-locally-constant).
(blueprint: lem-fin-lisse-field-site-perfect).

Proof: apply `finiteRing_derived_local_constancy` to obtain an etale covering and
bounded complexes of finite coefficient modules representing the restrictions of
C. Choose a vector-space basis in each term. Its coordinate isomorphism identifies
the associated constant sheaf with the constant finite free sheaf of the same rank,
so it is a retract with the coordinate isomorphism and its inverse. Exact constant
sheaves carry the zero terms outside the finite interval to zero. Finally use the
comparison between left-derived pullback and the derived functor of exact pullback
to identify the displayed restrictions with those in `IsSitePerfect`. This also
covers zero ranks and the empty scheme. -/
theorem finiteLisseField_sitePerfect (ℓ : ℕ) [Fact ℓ.Prime] (T : Scheme.{u})
    (C : DerivedCategoryModule (ULift.{u + 1} (ZMod ℓ)) T)
    (hbounded : ∃ a b : ℤ, a ≤ b ∧ ∀ i : ℤ, (i < a ∨ b < i) →
      IsZero ((_root_.DerivedCategory.homologyFunctor _ i).obj C))
    (hlisse : ∀ i : ℤ, Scheme.IsFiniteLocallyConstantSheaf
      ((_root_.DerivedCategory.homologyFunctor _ i).obj C)) :
    DerivedCategory.IsSitePerfect C := by
  obtain ⟨a, b, hab, hvan⟩ := hbounded
  obtain ⟨𝒰, h𝒰⟩ :=
    (finiteRing_derived_local_constancy T (ULift.{u + 1} (ZMod ℓ)) C
      ⟨a, b, hvan⟩ hlisse).1
  refine ⟨𝒰, fun i ↦ ?_⟩
  obtain ⟨E, ⟨a, b, hE⟩, hfinite, ⟨e⟩⟩ := h𝒰 i
  let F := constantSheaf (𝒰.X i).smallEtaleTopology
    (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))
  let P := (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj E
  refine ⟨P, a, b, ?_, ?_, ?_, ?_⟩
  · apply (CochainComplex.isStrictlyGE_iff P a).2
    intro n hn
    exact F.map_isZero (hE n (.inl hn))
  · apply (CochainComplex.isStrictlyLE_iff P b).2
    intro n hn
    exact F.map_isZero (hE n (.inr hn))
  · intro n
    have : Finite (E.X n) := hfinite n
    have : Module.Finite (ULift.{u + 1} (ZMod ℓ)) (E.X n) := inferInstance
    let eₙ :=
      (Module.finBasis (ULift.{u + 1} (ZMod ℓ)) (E.X n)).equivFun.toModuleIso
    exact ⟨_, ⟨⟨(F.mapIso eₙ).hom, (F.mapIso eₙ).inv, (F.mapIso eₙ).hom_inv_id⟩⟩⟩
  · exact ⟨(leftDerivedUpperStarIsoMapDerivedCategory _ (𝒰.f i)).app C ≪≫ e⟩

end AlgebraicGeometry.Etale
