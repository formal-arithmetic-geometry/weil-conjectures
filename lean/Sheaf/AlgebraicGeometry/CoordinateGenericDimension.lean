/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NA
-/
module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import WeilConjectures.AlgebraicGeometry.FunctionField
import WeilConjectures.AlgebraicGeometry.GenericFiber.CoordinateDimension

/-!
# Coordinate projections lower generic dimension

Source: blueprint, sec-smooth-purity, sk-prop-sf-cbc,
lem-fin-coordinate-generic-dimension (blueprint: lem-fin-coordinate-generic-dimension).

The generic fibre over `S` is the fibre at `genericPoint S`, equivalently base change to
its function field. A strict bound by the natural number `n` expresses dimension at most
`n - 1`, including `n = 0`: only the empty scheme has dimension strictly below zero.
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry

/-- Every coordinate projection of an open subscheme of a closed subscheme of affine
space lowers the dimension of the generic fibre by one. Empty fibres have dimension `⊥`.
Source: blueprint, sec-smooth-purity, sk-prop-sf-cbc,
lem-fin-coordinate-generic-dimension (blueprint: lem-fin-coordinate-generic-dimension).

Proof: The composite of the open immersion, closed immersion and affine-space projection
is locally of finite type. Identify the affine line indexed by `ULift (Fin 1)` with the
one indexed by `PUnit`, using the two constant reindexing maps. This isomorphism sends
generic point to generic point, so the inverse images of these points in `X` agree;
the fibre homeomorphisms therefore identify their topological Krull dimensions.
Apply the already proved source-library theorem
`topologicalKrullDim_fiber_genericPoint_add_one_le`, which applies to every locally
finite type morphism over an integral base. Combine its additive bound with `hdim`
and use the finite natural-number bound to obtain the strict inequality. The source
theorem proves the dimension drop by extending chains using a closed specialization
in the Jacobson generic fibre; no transcendence-degree calculation is needed here. -/
theorem coordinate_generic_fiber_dimension_lt
    (S : Scheme.{u}) [IsIntegral S] {m n : ℕ} {X Y : Scheme.{u}}
    (i : Y ⟶ AffineSpace (ULift.{u} (Fin m)) S) [IsClosedImmersion i]
    (j : X ⟶ Y) [IsOpenImmersion j]
    (hdim : topologicalKrullDim
      ((j ≫ i ≫ (AffineSpace (ULift.{u} (Fin m)) S ↘ S)).fiber (genericPoint S)) ≤
        (n : WithBot ℕ∞)) (r : Fin m) :
    topologicalKrullDim
      ((j ≫ i ≫ AffineSpace.reindex
        (fun _ : ULift.{u} (Fin 1) ↦ (ULift.up r : ULift.{u} (Fin m))) S).fiber
          (genericPoint (AffineSpace (ULift.{u} (Fin 1)) S))) < (n : WithBot ℕ∞) := by
  let e : AffineSpace (ULift.{u} (Fin 1)) S ≅ AffineSpace PUnit S :=
    { hom := AffineSpace.reindex (fun _ : PUnit ↦ (ULift.up 0 : ULift.{u} (Fin 1))) S
      inv := AffineSpace.reindex (fun _ : ULift.{u} (Fin 1) ↦ PUnit.unit) S
      hom_inv_id := by
        apply AffineSpace.hom_ext
        · simp
        · intro x
          simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
            AffineSpace.reindex_appTop_coord, Scheme.Hom.id_appTop]
          congr 1
          exact Subsingleton.elim _ _
      inv_hom_id := by
        apply AffineSpace.hom_ext
        · simp
        · intro x
          simp }
  have : IsIso e.hom := e.isIso_hom
  let f := j ≫ i ≫ (AffineSpace (ULift.{u} (Fin m)) S ↘ S)
  let a := j ≫ i ≫ AffineSpace.reindex
    (fun _ : ULift.{u} (Fin 1) ↦ (ULift.up r : ULift.{u} (Fin m))) S
  have hf : LocallyOfFiniteType f := by dsimp [f]; infer_instance
  have h := topologicalKrullDim_fiber_genericPoint_add_one_le f (a ≫ e.hom)
    (by simp [a, e, f])
  have he : e.hom (genericPoint (AffineSpace (ULift.{u} (Fin 1)) S)) =
      genericPoint (AffineSpace PUnit S) :=
    genericPoint_eq_of_isOpenImmersion e.hom
  have hd : topologicalKrullDim ((a ≫ e.hom).fiber
      (genericPoint (AffineSpace PUnit S))) =
      topologicalKrullDim (a.fiber
        (genericPoint (AffineSpace (ULift.{u} (Fin 1)) S))) := by
    rw [IsHomeomorph.topologicalKrullDim_eq _
      ((a ≫ e.hom).fiberHomeo _).isHomeomorph,
      IsHomeomorph.topologicalKrullDim_eq _ (a.fiberHomeo _).isHomeomorph]
    have hsets : (a ≫ e.hom) ⁻¹' {genericPoint (AffineSpace PUnit S)} =
        a ⁻¹' {genericPoint (AffineSpace (ULift.{u} (Fin 1)) S)} := by
      ext x
      change e.hom (a x) = _ ↔ a x = _
      rw [← he]
      exact e.hom.isOpenEmbedding.injective.eq_iff
    rw [hsets]
  rw [hd] at h
  exact ENat.WithBot.add_one_le_natCast_iff.mp (h.trans hdim)

end AlgebraicGeometry

