/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G2
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.Basic
import Sheaf.AlgebraicGeometry.FieldBaseChangeAffineCovers
import Sheaf.AlgebraicGeometry.DimensionAffineOpenCover
import Sheaf.AlgebraicGeometry.RationalPointLocalDimensionBaseChange
import Sheaf.AlgebraicGeometry.DimensionBaseChange
import WeilConjectures.AlgebraicGeometry.GroupScheme.Basic

/-!
# The dimension of a finite type group scheme at the identity

Source: blueprint `sk-i-cartier`, third proof paragraph, and the dimension paragraph of
`lem-wf-same-lie-closed-subgroup`.
(blueprint: lem-ag-group-identity-local-dimension)
-/

@[expose] public section

universe u

open CategoryTheory
open scoped MonObj

namespace AlgebraicGeometry.GrpObj

private theorem dimension_field_baseChange
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [LocallyOfFiniteType f] [Nonempty X] :
    topologicalKrullDim (Limits.pullback f
      (Spec.map (CommRingCat.ofHom (algebraMap k K))) : Scheme.{u}) =
      topologicalKrullDim X := by
  obtain ⟨hY, I, A, rings, algebras, hft, U, V, hU, hV, ⟨eU⟩, ⟨eV⟩⟩ :=
    exists_field_baseChange_affine_covers k K f
  let := rings
  let := algebras
  let := hft
  let Y := Limits.pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K)))
  have : Nonempty Y := hY
  rw [← Scheme.dim_eq_topologicalKrullDim Y, ← Scheme.dim_eq_topologicalKrullDim X]
  rw [Scheme.dim_eq_iSup_ringKrullDim_of_affineOpenCover Y V hV
    (fun i ↦ CommRingCat.of (TensorProduct k (A i) K)) eV,
    Scheme.dim_eq_iSup_ringKrullDim_of_affineOpenCover X U hU
    (fun i ↦ CommRingCat.of (A i)) eU]
  apply iSup_congr
  intro i
  exact dim_base_change.{u, u, u, u}.1 k K (A i)

private theorem rational_dimension_algClosed
    {k : Type u} [Field k] [IsAlgClosed k]
    (G : Over (Spec (.of k))) [GrpObj G]
    [LocallyOfFiniteType G.hom] [QuasiCompact G.hom]
    (p : Spec (.of k) ⟶ G.left) (hp : p ≫ G.hom = 𝟙 _) :
    ringKrullDim (G.left.presheaf.stalk
      (p (IsLocalRing.closedPoint k))) = topologicalKrullDim G.left := by
  let e := p (IsLocalRing.closedPoint k)
  have he : IsClosed ({e} : Set G.left) :=
    ((pointEquivClosedPoint G.hom) ⟨p, hp⟩).2
  have : CompactSpace G.left := QuasiCompact.compactSpace_of_compactSpace G.hom
  apply le_antisymm
  · rw [ringKrullDim_stalk_eq_coheight]
    exact coheight_le_topologicalKrullDim e
  · rw [← Scheme.dim_eq_topologicalKrullDim, Scheme.dim]
    refine iSup_le fun x ↦ ?_
    obtain ⟨y, hy, hyclosed⟩ := isClosed_closure.exists_closed_singleton
      (⟨x, subset_closure (Set.mem_singleton x)⟩ : (closure {x}).Nonempty)
    obtain ⟨φ, hφ⟩ := exists_homeomorph_apply_eq G he hyclosed
    have hdim : ringKrullDim (G.left.presheaf.stalk y) =
        ringKrullDim (G.left.presheaf.stalk e) := by
      rw [ringKrullDim_stalk_eq_coheight, ringKrullDim_stalk_eq_coheight, ← hφ]
      exact congrArg (fun n : ℕ∞ ↦ (n : WithBot ℕ∞))
        (φ.isOpenEmbedding.coheight_eq φ)
    rw [← hdim, ringKrullDim_stalk_eq_coheight, ringKrullDim_stalk_eq_coheight]
    apply WithBot.coe_le_coe.mpr
    apply Order.coheight_anti
    exact specializes_iff_mem_closure.mpr hy

/-- The local ring at the identity of a finite type group scheme has its global dimension.

Source: blueprint `sk-i-cartier`, third proof paragraph, and
`lem-wf-same-lie-closed-subgroup`, the dimension paragraph.
(blueprint: lem-ag-group-identity-local-dimension)

Proof: First extend the base field to its algebraic closure. For finite type schemes global
Krull dimension is unchanged by algebraic field extension. The local dimension at a rational
point is also unchanged: in an affine neighbourhood the extension is integral and faithfully
flat, and the local map at the lifted rational point has zero-dimensional fibre, so the
local dimensions agree. Over the algebraic closure every closed point is rational, by the
Nullstellensatz. Left translation by its value is an automorphism carrying the identity to
that point, so it induces an isomorphism of local rings. Every closed point consequently has
the same local dimension as the identity. A finite type scheme over a field is Noetherian;
its dimension is the supremum of the local dimensions at closed points (each point specializes
to a closed point and local dimension is nondecreasing under specialization). This supremum
is the common value, since the identity supplies a closed point. Descend the two dimensions
back to the original field. This argument uses neither smoothness nor characteristic zero,
and nilpotents do not affect any of the dimensions. -/
theorem localKrullDim_identity_eq_topologicalKrullDim
    {k : Type u} [Field k] (G : Over (Spec (.of k))) [GrpObj G]
    [LocallyOfFiniteType G.hom] [QuasiCompact G.hom] :
    ringKrullDim (G.left.presheaf.stalk
      (unitSection G (IsLocalRing.closedPoint k))) = topologicalKrullDim G.left := by
  let K := AlgebraicClosure k
  let g := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let H := (Over.pullback g).obj G
  let : GrpObj H := Functor.grpObjObj (F := Over.pullback g) (G := G)
  have : LocallyOfFiniteType H.hom :=
    inferInstanceAs (LocallyOfFiniteType (Limits.pullback.snd G.hom g))
  have : QuasiCompact H.hom :=
    inferInstanceAs (QuasiCompact (Limits.pullback.snd G.hom g))
  let p := unitSection G
  have hp : p ≫ G.hom = 𝟙 _ := unitSection_comp_hom G
  let q : Spec (.of K) ⟶ H.left :=
    Limits.pullback.lift (g ≫ p) (𝟙 _) (by simp [hp])
  have hq : q ≫ H.hom = 𝟙 _ := by simp [q, H]
  have : Nonempty G.left := ⟨p (IsLocalRing.closedPoint k)⟩
  calc
    ringKrullDim (G.left.presheaf.stalk (p (IsLocalRing.closedPoint k))) =
        ringKrullDim (H.left.presheaf.stalk (q (IsLocalRing.closedPoint K))) :=
      ringKrullDim_rationalPoint_field_baseChange G.hom p hp K q hq
        (by simp [q, g])
    _ = topologicalKrullDim H.left := rational_dimension_algClosed H q hq
    _ = topologicalKrullDim G.left := dimension_field_baseChange G.hom

end AlgebraicGeometry.GrpObj
