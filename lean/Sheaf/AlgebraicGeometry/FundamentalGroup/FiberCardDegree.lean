/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups Y2 and F6
-/
module

public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Basic
public import Mathlib.GroupTheory.Index
public import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
import WeilConjectures.AlgebraicGeometry.FiniteLocallyFreeDegreeLocallyConstant

/-!
# Geometric fibre cardinality and degree of finite étale covers

The finite locally free degree comparison complements the open-subgroup classification
in `WeilConjectures.AlgebraicGeometry.FundamentalGroup.OpenSubgroups`.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.FiniteEtale

open scoped FintypeCatDiscrete in
/-- A finite étale cover of a connected scheme has finite locally free degree equal to
its geometric fibre cardinality. The cover itself need not be connected or nonempty.

Source: Stacks Project, Tags 02K9 and 04MH, and the geometric-fibre computation used in
Tag 0BNB (blueprint: lem-fet-geometric-fiber-degree).

Proof: Let h be the pullback of the cover along the geometric point. The pullback
universal property identifies the geometric fibre with the Ω-points of h over Spec Ω.
Since h is affine, these points are the Ω-algebra homomorphisms from its global sections
to Ω. The étale-algebra cardinality theorem identifies their number with h.finrankΓ.
Base change identifies this with the original fibre degree at the image of the geometric
point. Finite étale morphisms are finite locally free, so their fibre degree is locally
constant. Connectedness makes it equal to this value everywhere. -/
private theorem degree_eq_fiber_card
    {Y : Scheme.{u}} [ConnectedSpace Y]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ Y)
    (P : Y.FiniteEtale) :
    P.obj.hom.IsFiniteLocallyFreeOfDegree (Nat.card ((fiber s).obj P)) :=
    open CategoryTheory.Limits CategoryTheory.PreGaloisCategory in by
  classical
  let f : P.obj.left ⟶ Y := P.obj.hom
  let h := pullback.snd f s
  have : IsFinite f := P.property
  have : f.IsFiniteLocallyFree := ⟨⟩
  have : IsAffine (Limits.pullback f s) := isAffine_of_isAffineHom h
  let := h.ΓAlgebra
  have := h.etale_ΓAlgebra
  have hid : Spec.map (CommRingCat.ofHom (algebraMap Ω Ω)) = 𝟙 _ := by
    rw [Algebra.algebraMap_self]
    exact Spec.map_id _
  let e : (fiber s).obj P ≃
      (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Ω Ω))) ⟶ Over.mk h) :=
    { toFun z := Over.homMk
        (pullback.lift z.left (Spec.map (CommRingCat.ofHom (algebraMap Ω Ω)))
          (by simpa [hid] using Over.w z)) (by simp [h])
      invFun z := Over.homMk (z.left ≫ pullback.fst f s) (by
        change (z.left ≫ pullback.fst f s) ≫ f = s
        calc
          (z.left ≫ pullback.fst f s) ≫ f = (z.left ≫ pullback.snd f s) ≫ s := by
            rw [Category.assoc, pullback.condition, Category.assoc]
          _ = Spec.map (CommRingCat.ofHom (algebraMap Ω Ω)) ≫ s :=
            congrArg (fun t ↦ t ≫ s) (Over.w z)
          _ = s := by rw [hid, Category.id_comp])
      left_inv z := by apply fiber_ext s; simp
      right_inv z := by
        apply Over.OverMorphism.ext
        apply pullback.hom_ext
        · simp
        · simpa [h] using (Over.w z).symm }
  have hc : Nat.card ((fiber s).obj P) = h.finrankΓ := by
    rw [Nat.card_congr (e.trans (h.overHomEquivAlgHom Ω)),
      Algebra.Etale.natCard_algHom_eq_finrank]
    rfl
  obtain ⟨z⟩ := (inferInstance : Nonempty (Spec (.of Ω)))
  have hdeg : f.fiberDegree (s z) = h.finrankΓ := by
    exact (f.fiberDegree_of_isPullback (.of_hasPullback f s) z).symm.trans
      (fiberDegree_eq_finrankΓ h z)
  refine { toIsFiniteLocallyFree := inferInstance, fiberDegree_eq := ?_ }
  intro y
  have hloc := (finiteLocallyFree_fiberDimension_isLocallyConstant f).2.1
  exact (hloc.apply_eq_of_preconnectedSpace y (s z)).trans (hdeg.trans hc.symm)

open CategoryTheory.PreGaloisCategory in
/-- A connected finite étale cover has finite locally free degree equal to the index
of the stabilizer of a geometric fibre point in any fundamental-group model.

Source: Stacks Project, Tags 0BNB, 0BND, 02K9 and 04MH
(blueprint: lem-fet-geometric-fiber-degree).

Proof: The geometric pullback is affine étale over the separably closed field Ω.
Its Ω-points correspond to algebra homomorphisms from its global sections to Ω,
whose cardinality is its vector-space dimension. Base change and local constancy
of finite locally free degree on the connected base therefore give degree equal
to geometric fibre cardinality (`degree_eq_fiber_card`). The transitive-action
orbit-stabilizer theorem identifies this cardinality with the stabilizer index. -/
theorem isFiniteLocallyFreeOfDegree_index_stabilizer
    {Y : Scheme.{u}} [ConnectedSpace Y]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ Y)
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [∀ P, MulAction G ((fiber s).obj P)] [IsFundamentalGroup (fiber s) G]
    (P : Y.FiniteEtale) [IsConnected P] (p : (fiber s).obj P) :
    P.obj.hom.IsFiniteLocallyFreeOfDegree (MulAction.stabilizer G p).index := by
  rw [MulAction.index_stabilizer_of_transitive]
  exact degree_eq_fiber_card s P

end AlgebraicGeometry.Scheme.FiniteEtale
