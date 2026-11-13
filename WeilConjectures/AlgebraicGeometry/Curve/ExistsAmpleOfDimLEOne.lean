/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.Topology.KrullDimension
public import WeilConjectures.AlgebraicGeometry.Ample
import WeilConjectures.AlgebraicGeometry.Ample.AmpleOnReductionNoetherian
import WeilConjectures.AlgebraicGeometry.AmpleIso
import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.Curve.ExistsAmpleOfReducedDimLEOne
import WeilConjectures.AlgebraicGeometry.Picard.PicardLift
import WeilConjectures.AlgebraicGeometry.ReductionUniversalHomeomorphism

/-! # Ample invertible modules in dimension at most one

Source: Stacks Project, Varieties, Lemma 0A25 and Proposition 09NZ.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

/-- A separated finite-type scheme over a field of topological dimension at most one
has an ample invertible module, including when the scheme is empty.
Source: Stacks Project, Varieties, Lemma 0A25, using Proposition 09NZ. -/
theorem exists_isAmple_of_dim_le_one {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (hdim : topologicalKrullDim X ≤ 1) :
    ∃ L : X.Modules, ∃ hL : L.IsInvertible, @IsAmple X L hL := by
  have : IsNoetherian X := isNoetherian_of_locallyOfFiniteType f
  have : X.IsSeparated := HasAffineProperty.iff_of_isAffine.mp
    (inferInstance : IsSeparated f)
  let Z := X.nilradical.subscheme
  let i : Z ⟶ X := X.nilradical.subschemeι
  have hred := reduction_isReduced_isClosedImmersion_isSurjective_isUniversalHomeomorphism X
  have : IsReduced Z := hred.1
  have : IsClosedImmersion i := hred.2.1
  have : IsNoetherian Z := isNoetherian_of_locallyOfFiniteType i
  have : Z.IsSeparated := HasAffineProperty.iff_of_isAffine.mp
    (inferInstance : IsSeparated (i ≫ f))
  have hi : IsHomeomorph i.base :=
    isHomeomorph_iff_isEmbedding_surjective.mpr ⟨i.isEmbedding, hred.2.2.1.surj⟩
  have hZdim : topologicalKrullDim Z ≤ 1 := by
    rw [IsHomeomorph.topologicalKrullDim_eq i.base hi]
    exact hdim
  obtain ⟨N, hN, hNamp⟩ := exists_isAmple_of_reduced_dim_le_one Z hZdim
  obtain ⟨L, hL, ⟨e⟩⟩ :=
    exists_isInvertible_tensorPullback_iso_of_isClosedImmersion i hdim N hN
  have : L.IsInvertible := hL
  have : N.IsInvertible := hN
  have : ((tensorPullback i).obj L).IsInvertible :=
    ((invertible_pullback_tensor i).1 L).2
  refine ⟨L, hL, ?_⟩
  apply (isAmple_iff_of_isClosedImmersion_of_isHomeomorph i hi L).mp
  exact (isAmple_iff_of_iso e).mpr hNamp

end AlgebraicGeometry.Scheme.Modules
