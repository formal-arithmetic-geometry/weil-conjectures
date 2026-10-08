/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Stalk
public import WeilConjectures.Mathlib.Topology.Connected.Clopen
public import WeilConjectures.Mathlib.Topology.NoetherianSpace

/-!
# Connected locally noetherian schemes with integral local rings

## Main statements

- `AlgebraicGeometry.irreducibleSpace_of_isDomain_stalk`: a connected locally noetherian scheme
  all of whose local rings are integral domains is irreducible.
- `AlgebraicGeometry.isNoetherian_of_locallyOfFiniteType`: a scheme quasi-compact and locally of
  finite type over a noetherian scheme is noetherian.
-/

@[expose] public section

universe u

open TopologicalSpace

namespace AlgebraicGeometry

/-- A connected locally noetherian scheme all of whose local rings are integral domains is
irreducible.

Each point `x` lies in a unique irreducible component of a noetherian affine open neighbourhood,
since the generic points of these components are generalizations of `x`, and the set of
generalizations of `x` is irreducible, being the image of `Spec 𝒪_{X, x}`. So every point has an
irreducible open neighbourhood, and a connected locally irreducible space is irreducible. -/
theorem irreducibleSpace_of_isDomain_stalk (X : Scheme.{u}) [IsLocallyNoetherian X]
    [ConnectedSpace X] (h : ∀ x : X, IsDomain (X.presheaf.stalk x)) : IrreducibleSpace X := by
  refine irreducibleSpace_of_forall_exists_isPreirreducible fun x ↦ ?_
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  have hVN : NoetherianSpace V := noetherianSpace_of_isAffineOpen V hV
  have hS : IsIrreducible {y | y ⤳ x} := by
    rw [← X.range_fromSpecStalk, ← Set.image_univ]
    exact (IrreducibleSpace.isIrreducible_univ _).image _
      (X.fromSpecStalk x).continuous.continuousOn
  have hS' : IsPreirreducible (((↑) : V → X) ⁻¹' {y | y ⤳ x}) :=
    hS.isPreirreducible.preimage V.2.isOpenEmbedding_subtypeVal
  obtain ⟨U, hU, hxU, hUirr⟩ := @NoetherianSpace.exists_isOpen_isPreirreducible V _ hVN
    (⟨x, hxV⟩ : V) fun Z₁ hZ₁ Z₂ hZ₂ hx₁ hx₂ ↦ by
      have hirr : IsIrreducible (closure (((↑) : V → X) ⁻¹' {y | y ⤳ x})) :=
        IsIrreducible.closure ⟨⟨⟨x, hxV⟩, specializes_rfl⟩, hS'⟩
      obtain ⟨W, hW, hSW⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible _ hirr
      have key : ∀ Z ∈ irreducibleComponents V, (⟨x, hxV⟩ : V) ∈ Z → Z = W := fun Z hZ hxZ ↦ by
        obtain ⟨η, hη⟩ := QuasiSober.sober hZ.1 (isClosed_of_mem_irreducibleComponents _ hZ)
        refine (hZ.eq_of_ge hW.1 ?_).symm
        refine hη.symm.trans_subset (subset_trans ?_ hSW)
        exact closure_mono (Set.singleton_subset_iff.mpr
          ((hη.specializes hxZ).map continuous_subtype_val))
      exact (key Z₁ hZ₁ hx₁).trans (key Z₂ hZ₂ hx₂).symm
  exact ⟨((↑) : V → X) '' U, V.2.isOpenMap_subtype_val U hU, ⟨_, hxU, rfl⟩,
    hUirr.image _ continuous_subtype_val.continuousOn⟩

/-- A scheme that is quasi-compact and locally of finite type over a noetherian scheme is
noetherian. -/
theorem isNoetherian_of_locallyOfFiniteType {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] [QuasiCompact f] [IsNoetherian Y] : IsNoetherian X :=
  have := LocallyOfFiniteType.isLocallyNoetherian f
  have := QuasiCompact.compactSpace_of_compactSpace f
  {}

end AlgebraicGeometry
