/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact

import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.GenericComponentsSplit
import WeilConjectures.AlgebraicGeometry.GeometricGenericCoverSpread

/-!
# Spreading the incidence data of geometric generic components

## References

* [Stacks, Tag 055G]
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Topology

namespace AlgebraicGeometry

/-- The finite component cover of a split generic fibre spreads with its intersection
edges, independently of whether the generic fibre is connected (Stacks, Tag 055G). -/
theorem exists_open_generic_fibre_incidence_spread {X S : Scheme.{u}}
    [IrreducibleSpace S] (f : X ⟶ S) [LocallyOfFiniteType f] [QuasiCompact f] :
    ∃ (L : Type u) (_ : Field L)
      (yη : Spec (CommRingCat.of L) ⟶
        Spec (CommRingCat.of (S.residueField (genericPoint S))))
      (I : Type u) (_ : Finite I)
      (A : I → Set ↥(pullback
        (f.fiberToSpecResidueField (genericPoint S)) yη)) (W : Set S),
      (∀ i, IsClosed (A i)) ∧ (∀ i, IsIrreducible (A i)) ∧
      (⋃ i, A i) = Set.univ ∧ IsOpen W ∧ genericPoint S ∈ W ∧
      ∀ s ∈ W, ∀ (K : Type u) (_ : Field K)
        (y : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of (S.residueField s))),
        ∃ (Z : Scheme.{u}) (p : Z ⟶ pullback (f.fiberToSpecResidueField s) y)
          (B : I → Set Z), Surjective p ∧
          (∀ i, IsIrreducible (B i)) ∧ (⋃ i, B i) = Set.univ ∧
          ∀ i j, (A i ∩ A j).Nonempty → (B i ∩ B j).Nonempty := by
  classical
  have : LocallyOfFiniteType (f.fiberToSpecResidueField (genericPoint S)) := by
    dsimp [Scheme.Hom.fiberToSpecResidueField]
    infer_instance
  have : QuasiCompact (f.fiberToSpecResidueField (genericPoint S)) := by
    dsimp [Scheme.Hom.fiberToSpecResidueField]
    infer_instance
  obtain ⟨L, hL, yη, hfinite, hetale, hgeom⟩ :=
    exists_finite_etale_geometric_component_extension
      (f.fiberToSpecResidueField (genericPoint S))
  let : Field L := hL
  let : IsFinite yη := hfinite
  let : Etale yη := hetale
  let G := pullback (f.fiberToSpecResidueField (genericPoint S)) yη
  let I := ↥(irreducibleComponents ↥G)
  have : IsNoetherian G := {}
  let : Finite I := (finite_irreducibleComponents_of_isNoetherian (X := G)).to_subtype
  let A : I → Set G := fun i ↦ i.val
  have hclosed : ∀ i, IsClosed (A i) := fun i ↦
    isClosed_of_mem_irreducibleComponents _ i.property
  have hirred : ∀ i, IsIrreducible (A i) := fun i ↦ i.property.1
  have hcover : (⋃ i, A i) = Set.univ := by
    simpa only [A, I, Set.iUnion_coe_set, Set.sUnion_eq_biUnion] using
      (sUnion_irreducibleComponents (X := ↥G))
  obtain ⟨W, hopen, hη, hspread⟩ :=
    exists_open_spreading_geometric_generic_cover f yη A hclosed hcover
      (fun i ↦ hgeom i.val i.property)
  exact ⟨L, hL, yη, I, inferInstance, A, W, hclosed, hirred, hcover, hopen, hη, hspread⟩

end AlgebraicGeometry
