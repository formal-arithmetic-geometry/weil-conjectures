/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Mathlib.Topology.KrullDimension
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.OpenImmersion

import WeilConjectures.AlgebraicGeometry.FieldBaseChangeDimension
import WeilConjectures.AlgebraicGeometry.DenseCompactification

/-!
# Dimension after field extension and dense open restriction

Source: Stacks Project, Tags 00P3 and 0A21.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Dimension of a finite type scheme over a field is unchanged by any field extension
or any dense open immersion. Source: Stacks Project, Tags 00P3 and 0A21. -/
theorem topologicalKrullDim_fieldExtension_and_denseOpen
    {K : Type u} [Field K] {X : Scheme.{u}} [X.Over (Spec (.of K))]
    [LocallyOfFiniteType (X ↘ Spec (.of K))] [QuasiCompact (X ↘ Spec (.of K))] :
    (∀ (L : Type u) [Field L] [Algebra K L],
      topologicalKrullDim (pullback (X ↘ Spec (.of K))
        (Spec.map (CommRingCat.ofHom (algebraMap K L))) : Scheme.{u}) =
        topologicalKrullDim X) ∧
    (∀ (U : Scheme.{u}) (j : U ⟶ X) [IsOpenImmersion j],
      DenseRange j → topologicalKrullDim U = topologicalKrullDim X) := by
  constructor
  · intro L _ _
    exact topologicalKrullDim_pullback_eq_of_field _ _
  · intro U j _ hd
    apply le_antisymm j.isOpenEmbedding.isInducing.topologicalKrullDim_le
    exact (topologicalKrullDim_le_of_dense (X ↘ Spec (.of K)) j.opensRange hd).trans_eq
      j.isOpenEmbedding.isEmbedding.topologicalKrullDim_eq_range.symm

end AlgebraicGeometry
