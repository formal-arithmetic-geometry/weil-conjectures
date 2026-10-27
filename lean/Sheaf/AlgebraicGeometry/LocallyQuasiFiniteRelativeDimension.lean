/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF contributors
-/
module

public import WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism
public import WeilConjectures.Mathlib.Topology.KrullDimension
import WeilConjectures.AlgebraicGeometry.QuasiFiniteAtPointIsolated
import WeilConjectures.AlgebraicGeometry.IsolatedFiberPointQuasiFiniteAffinePairs
import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Locally quasi-finite morphisms and relative dimension zero

Source: Stacks Project, Morphisms of Schemes, Tag 0397, lemma-locally-quasi-finite-rel-dimension-0
(blueprint: lem-trf-locally-quasi-finite-relative-dimension-zero)
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Hom

/-- A morphism locally of finite type is locally quasi-finite exactly when every fibre has
local topological Krull dimension zero at the point corresponding to each source point.

Source: Stacks Project, Morphisms of Schemes, Tag 0397, lemma-locally-quasi-finite-rel-dimension-0
(blueprint: lem-trf-locally-quasi-finite-relative-dimension-zero).
Proof: Fix a source point and choose affine neighbourhoods of it and of its image. The induced
finite-type ring map identifies the corresponding affine fibre with an open neighbourhood of the
point in the scheme-theoretic fibre, and the canonical homeomorphisms preserve local Krull
dimension. The affine ring equivalence between quasi-finiteness at a prime and zero local fibre
dimension gives the forward and reverse implications. Quantifying over all source points yields
the stated equivalence; for an empty source both sides are vacuous.
-/
theorem isLocallyQuasiFinite_iff_topologicalKrullDimAt_fiber_eq_zero
    {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S) [AlgebraicGeometry.LocallyOfFiniteType f] :
    f.IsLocallyQuasiFinite ↔
      ∀ x : X, topologicalKrullDimAt (f.asFiber x) = 0 := by
  classical
  change (∀ x : X, f.IsQuasiFiniteAtPoint x) ↔ _
  -- Stacks 0397, second proof: reduce quasi-finiteness to isolation in the fibre.
  have hpoint (x : X) : f.IsQuasiFiniteAtPoint x ↔ IsOpen {f.asFiber x} := by
    refine ⟨fun hx ↦ (quasiFiniteAtPoint_isolated_in_fiber f x hx).1, fun hx ↦ ?_⟩
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
      S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUV⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open hxV (f ⁻¹ᵁ V).isOpen
    exact ⟨U, hxU, hU, V, hV, hUV,
      f.isQuasiFiniteAtPrime_of_isOpen_singleton_asFiber x hx U V hU hV hxU hUV⟩
  simp_rw [hpoint]
  constructor
  · intro h x
    let Y := f.fiber (f x)
    let y : Y := f.asFiber x
    change topologicalKrullDimAt y = 0
    let U : TopologicalSpace.Opens Y := ⟨{y}, h x⟩
    have hyU : y ∈ U := Set.mem_singleton y
    have : Subsingleton U := ⟨fun a b ↦ Subtype.ext (a.property.trans b.property.symm)⟩
    have hnonneg (V : TopologicalSpace.Opens Y) (hyV : y ∈ V) :
        0 ≤ topologicalKrullDim V := by
      have : Nonempty (TopologicalSpace.IrreducibleCloseds V) :=
        ⟨⟨closure {(⟨y, hyV⟩ : V)}, isIrreducible_singleton.closure, isClosed_closure⟩⟩
      exact Order.krullDim_nonneg
    apply le_antisymm
    · exact (iInf₂_le U hyU).trans (topologicalKrullDim_zero_of_discreteTopology U)
    · exact le_iInf₂ hnonneg
  · intro h x
    let Y := f.fiber (f x)
    let y : Y := f.asFiber x
    have : LocallyOfFiniteType (f.fiberToSpecResidueField (f x)) := by
      change LocallyOfFiniteType (CategoryTheory.Limits.pullback.snd _ _)
      infer_instance
    have : IsLocallyNoetherian Y :=
      LocallyOfFiniteType.isLocallyNoetherian (f.fiberToSpecResidueField (f x))
    obtain ⟨_, ⟨W, hW, rfl⟩, hyW, -⟩ :=
      Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
    have : IsNoetherianRing Γ(Y, W) :=
      IsLocallyNoetherian.component_noetherian ⟨W, hW⟩
    have : TopologicalSpace.NoetherianSpace W := noetherianSpace_of_isAffineOpen W hW
    let w : W := ⟨y, hyW⟩
    have hw : topologicalKrullDimAt w = 0 :=
      (W.isOpen.topologicalKrullDimAt_eq hyW).trans (h x)
    have hlt : topologicalKrullDimAt w < (0 : WithBot ℕ∞) + 1 := by
      rw [hw]
      exact ENat.WithBot.lt_add_one_iff.mpr le_rfl
    change (⨅ (V : TopologicalSpace.Opens W) (_ : w ∈ V), topologicalKrullDim V) < _ at hlt
    obtain ⟨V, hV⟩ := iInf_lt_iff.mp hlt
    obtain ⟨hwV, hdim⟩ := iInf_lt_iff.mp hV
    have : TopologicalSpace.NoetherianSpace V :=
      Topology.IsInducing.subtypeVal.noetherianSpace
    have hdimV : topologicalKrullDim V ≤ 0 := ENat.WithBot.lt_add_one_iff.mp hdim
    have hfinite :=
      IsClosed.finite_and_isClosed_singleton_of_topologicalKrullDim_le_zero
        (X := V) (Z := (Set.univ : Set V)) isClosed_univ (by
          rw [IsHomeomorph.topologicalKrullDim_eq _ (Homeomorph.Set.univ V).isHomeomorph]
          exact hdimV)
    have : Finite V := Set.finite_univ_iff.mp hfinite.1
    have : T1Space V := ⟨fun z ↦ by simpa using hfinite.2 z trivial⟩
    have : DiscreteTopology V := inferInstance
    have hopenW : IsOpen ({w} : Set W) := by
      simpa using V.isOpen.isOpenMap_subtype_val _
        (isOpen_discrete ({⟨w, hwV⟩} : Set V))
    simpa using W.isOpen.isOpenMap_subtype_val _ hopenW

end AlgebraicGeometry.Scheme.Hom
