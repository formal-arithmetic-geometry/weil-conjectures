/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.Topology.KrullDimension
import WeilConjectures.Mathlib.Topology.KrullDimension
import WeilConjectures.AlgebraicGeometry.Affine.Limit.AffineLimitFibreDimensionBoundCore

/-!
# Fibre dimension bounds descend in affine inverse systems
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- An upper bound on all fibre dimensions of a directed colimit of finite type ring maps
already holds at one stage, provided the base-change comparison maps are surjective.

The comparison is expressed by the commutative-ring pushout, canonically the tensor product
by `CommRingCat.pushoutCoconeIsColimit`. The fibres are affine pullbacks, identified by
`pullbackSpecIso` with spectra of the tensor products with the residue fields. Thus empty
fibres have dimension bottom and are included. -/
theorem exists_stage_fibre_dimension_le
    {I : Type u} [PartialOrder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (A C : I ⥤ CommRingCat.{u}) (φ : A ⟶ C)
    (hfinite : ∀ i : I, (φ.app i).hom.FiniteType)
    (hsurj : ∀ (i j : I) (hij : i ≤ j),
      Function.Surjective
        (pushout.desc (φ.app j) (C.map (homOfLE hij))
          (φ.naturality (homOfLE hij))).hom)
    (d : ℕ)
    (hbound : ∀ (p : Ideal ↥(colimit A)) [p.IsPrime],
      topologicalKrullDim
        ↥(pullback (Spec.map (colimMap φ))
          (Spec.map (CommRingCat.ofHom (algebraMap ↥(colimit A) p.ResidueField))) : Scheme.{u}) ≤
        (d : WithBot ℕ∞)) :
    ∃ i : I, ∀ (p : Ideal (A.obj i)) [p.IsPrime],
      topologicalKrullDim
        ↥(pullback (Spec.map (φ.app i))
          (Spec.map (CommRingCat.ofHom (algebraMap (A.obj i) p.ResidueField))) : Scheme.{u}) ≤
        (d : WithBot ℕ∞) := by
  classical
  by_contra h
  apply fibre_dimension_contradiction_of_all_stages_bad A C φ hfinite hsurj d hbound
  intro i
  push Not at h
  obtain ⟨p, hp, hdim⟩ := h i
  exact ⟨⟨p, hp⟩, hdim⟩

end AlgebraicGeometry
