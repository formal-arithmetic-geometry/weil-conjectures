/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact

import WeilConjectures.AlgebraicGeometry.GenericOpenFibreDensity

/-! # Generic affine chart and geometric fibre density

## References

* Stacks, Tags 0559 and 054X
-/

@[expose] public section

universe u
open CategoryTheory Limits Topology
namespace AlgebraicGeometry

/-- An open source subscheme with geometrically irreducible generic fibre has dense
image in every geometric fibre after shrinking the base (Stacks, Tag 054X). -/
theorem exists_open_geometric_fibre_dense_of_open {X T : Scheme.{u}}
    (f : X ⟶ T) [LocallyOfFiniteType f] [QuasiCompact f]
    (W : X.Opens) (η : T) (hη : IsGenericPoint η Set.univ)
    (hgeom : GeometricallyIrreducible (f.fiberToSpecResidueField η))
    (hWgeom : GeometricallyIrreducible ((W.ι ≫ f).fiberToSpecResidueField η)) :
    ∃ U : T.Opens, η ∈ U ∧
      ∀ (t : T), t ∈ U → ∀ (K : Type u) [Field K]
        (z : Spec (.of K) ⟶ Spec (T.residueField t)),
        DenseRange (pullback.map ((W.ι ≫ f).fiberToSpecResidueField t) z
          (f.fiberToSpecResidueField t) z
          (pullback.map (W.ι ≫ f) (T.fromSpecResidueField t) f
            (T.fromSpecResidueField t) W.ι (𝟙 _) (𝟙 _) (by simp) (by simp))
          (𝟙 _) (𝟙 _) (by simp [Scheme.Hom.fiberToSpecResidueField]) (by simp)) := by
  have := hgeom
  have := hWgeom
  have : IrreducibleSpace (f.fiber η) :=
    GeometricallyIrreducible.irreducibleSpace_of_subsingleton
      (f.fiberToSpecResidueField η)
  have : IrreducibleSpace ((W.ι ≫ f).fiber η) :=
    GeometricallyIrreducible.irreducibleSpace_of_subsingleton
      ((W.ι ≫ f).fiberToSpecResidueField η)
  let i := pullback.map (W.ι ≫ f) (T.fromSpecResidueField η) f
    (T.fromSpecResidueField η) W.ι (𝟙 _) (𝟙 _) (by simp) (by simp)
  have : Nonempty ↥(pullback (W.ι ≫ f) (T.fromSpecResidueField η)) :=
    inferInstanceAs (Nonempty ((W.ι ≫ f).fiber η))
  have : PreirreducibleSpace ↥(pullback f (T.fromSpecResidueField η)) :=
    inferInstanceAs (PreirreducibleSpace (f.fiber η))
  have hi : DenseRange i :=
    i.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace i
  have hrange (t : T) :
      Set.range (pullback.map (W.ι ≫ f) (T.fromSpecResidueField t) f
        (T.fromSpecResidueField t) W.ι (𝟙 _) (𝟙 _) (by simp) (by simp)) =
        (f.fiberι t) ⁻¹' (W : Set X) := by
    rw [Scheme.Pullback.range_map]
    simp [Scheme.Hom.fiberι]
    rfl
  have hdense : Dense ((f.fiberι η) ⁻¹' (W : Set X)) := by
    rw [← hrange η]
    exact hi
  obtain ⟨U, hηU, hU⟩ := exists_open_fibre_dense_of_generic_dense f W η hη hdense
  refine ⟨U, hηU, ?_⟩
  intro t ht K _ z
  rw [denseRange_iff_closure_range]
  rw [Scheme.Pullback.range_map]
  have hid : Set.range (𝟙 (Spec (.of K))) = Set.univ := by
    exact Set.range_eq_univ.mpr (Scheme.Hom.surjective (𝟙 (Spec (.of K))))
  rw [hid, Set.preimage_univ, Set.inter_univ]
  have hd : Dense (Set.range (pullback.map (W.ι ≫ f) (T.fromSpecResidueField t) f
      (T.fromSpecResidueField t) W.ι (𝟙 _) (𝟙 _) (by simp) (by simp))) := by
    rw [hrange t]
    exact hU t ht
  exact (hd.preimage (pullback.fst (f.fiberToSpecResidueField t) z).isOpenMap).closure_eq

end AlgebraicGeometry
