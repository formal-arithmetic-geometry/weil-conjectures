/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NK
-/
module

public import Sheaf.AlgebraicGeometry.InvertibleTorsionOrders
public import WeilConjectures.AlgebraicGeometry.TorsionEtaleSheaf
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint

/-!
# The colimit description of invertible orders

Source: blueprint `sec-smooth-purity/sk-prop-sf-kunneth-ordinary/`
`lem-kun-invertible-orders-colimit.md` (blueprint: lem-kun-invertible-orders-colimit).

The diagram, its cocone of kernel inclusions, and the induced comparison are explicit.
The index inherits divisibility from `PNat.DvdOrder`; no bounded exponent is imposed.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- The diagram `n ↦ F[n]` over positive integers invertible in `K`, ordered by divisibility.
Transitions are the canonical kernel lifts of the kernel inclusions into `F`.
Source: blueprint `sec-smooth-purity/sk-prop-sf-kunneth-ordinary/`
`lem-kun-invertible-orders-colimit.md`, displayed colimit and its index
(blueprint: lem-kun-invertible-orders-colimit). -/
noncomputable def fieldInvertibleTorsionDiagram (K : Type u) [Field K] {T : Scheme.{u}}
    (F : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    ObjectProperty.FullSubcategory
      (fun n : PNat.DvdOrder ↦ n.val ∈ Etale.invertibleTorsionOrders K) ⥤
      Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1} where
  obj n := Etale.etaleNTorsion F n.obj.val
  map {n m} hnm := kernel.lift (m.obj.val • 𝟙 F) (kernel.ι (n.obj.val • 𝟙 F))
    (torsionKernelTransition_condition F n.obj m.obj hnm.hom.down.down)
  map_id n := torsionKernelTransition_id F n.obj
  map_comp {n m k} hnm hmk :=
    (torsionKernelTransition_comp F n.obj m.obj k.obj hnm.hom.down.down hmk.hom.down.down).symm

/-- The kernel inclusions `F[n] ⟶ F`, as a cocone on the invertible-order diagram.
Source: blueprint `sec-smooth-purity/sk-prop-sf-kunneth-ordinary/`
`lem-kun-invertible-orders-colimit.md`, canonical comparison clause
(blueprint: lem-kun-invertible-orders-colimit). -/
noncomputable def fieldInvertibleTorsionCocone (K : Type u) [Field K] {T : Scheme.{u}}
    (F : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    Cocone (fieldInvertibleTorsionDiagram K F) where
  pt := F
  ι :=
    { app := fun n ↦ kernel.ι (n.obj.val • 𝟙 F)
      naturality := by
        intro n m hnm
        simp [fieldInvertibleTorsionDiagram] }

/-- The canonical map `colim F[n] ⟶ F` induced by the kernel inclusions.
Source: blueprint `sec-smooth-purity/sk-prop-sf-kunneth-ordinary/`
`lem-kun-invertible-orders-colimit.md`, interpretation of the displayed equality
(blueprint: lem-kun-invertible-orders-colimit). -/
noncomputable def fieldInvertibleTorsionComparison (K : Type u) [Field K] {T : Scheme.{u}}
    (F : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    colimit (fieldInvertibleTorsionDiagram K F) ⟶ F :=
  colimit.desc (fieldInvertibleTorsionDiagram K F) (fieldInvertibleTorsionCocone K F)

private theorem invertibleTorsionIndex_filtered (K : Type u) [Field K] :
    IsFiltered (ObjectProperty.FullSubcategory
      (fun n : PNat.DvdOrder ↦ n.val ∈ Etale.invertibleTorsionOrders K)) where
  nonempty := ⟨⟨⟨1, Nat.one_pos⟩, by
    refine ⟨Nat.one_pos, ?_⟩
    norm_num [PNat.DvdOrder.val, PNat.DvdOrder.toPNat]⟩⟩
  cocone_objs n m := by
    let k : ObjectProperty.FullSubcategory
        (fun n : PNat.DvdOrder ↦ n.val ∈ Etale.invertibleTorsionOrders K) :=
      ⟨⟨n.obj.val * m.obj.val, Nat.mul_pos (PNat.DvdOrder.val_pos n.obj)
        (PNat.DvdOrder.val_pos m.obj)⟩,
        Nat.mul_pos (PNat.DvdOrder.val_pos n.obj)
        (PNat.DvdOrder.val_pos m.obj), by
          change ((n.obj.val * m.obj.val : ℕ) : K) ≠ 0
          rw [Nat.cast_mul]
          exact mul_ne_zero n.property.2 m.property.2⟩
    exact ⟨k, ObjectProperty.homMk (homOfLE (dvd_mul_right _ _)),
      ObjectProperty.homMk (homOfLE (dvd_mul_left _ _)), trivial⟩
  cocone_maps _ _ f g := ⟨_, 𝟙 _, by subsingleton⟩

private theorem invertibleTorsion_map_iff (K : Type u) [Field K] {T : Scheme.{u}}
    (F : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})
    (E : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1} ⥤ AddCommGrpCat.{u + 1})
    [E.Additive] [PreservesFiniteLimits E] [PreservesColimitsOfSize.{u, u} E] :
    IsIso (E.map (fieldInvertibleTorsionComparison K F)) ↔
      ∀ x : E.obj F, ∃ n : ℕ, n ∈ Etale.invertibleTorsionOrders K ∧ n • x = 0 := by
  classical
  have := invertibleTorsionIndex_filtered K
  have := preservesSmallestColimits_of_preservesColimits E
  have := preservesSmallestFilteredColimits_of_preservesFilteredColimits
    (CategoryTheory.forget AddCommGrpCat.{u + 1})
  let D := fieldInvertibleTorsionDiagram K F
  let φ := fieldInvertibleTorsionComparison K F
  have hc := isColimitOfPreserves E (colimit.isColimit D)
  have hcomp (n : ObjectProperty.FullSubcategory
      (fun n : PNat.DvdOrder ↦ n.val ∈ Etale.invertibleTorsionOrders K)) :
      E.map (colimit.ι D n) ≫ E.map φ = E.map (kernel.ι (n.obj.val • 𝟙 F)) := by
    rw [← E.map_comp]
    congr 1
    exact colimit.ι_desc (fieldInvertibleTorsionCocone K F) n
  have hmono : Mono (E.map φ) := by
    apply (AddCommGrpCat.mono_iff_injective _).mpr
    apply (injective_iff_map_eq_zero _).mpr
    intro x hx
    obtain ⟨n, y, rfl⟩ := Concrete.isColimit_exists_rep (D ⋙ E) hc x
    have hy : E.map (kernel.ι (n.obj.val • 𝟙 F)) y = 0 := by
      rw [← hcomp n]
      exact hx
    have hinj := (AddCommGrpCat.mono_iff_injective
      (E.map (kernel.ι (n.obj.val • 𝟙 F)))).mp (inferInstance)
    have : y = 0 := hinj (by simpa using hy)
    rw [this]
    exact map_zero (E.map (colimit.ι D n)).hom
  constructor
  · intro h
    have := h
    intro x
    obtain ⟨y, hy⟩ := (AddCommGrpCat.epi_iff_surjective (E.map φ)).mp inferInstance x
    obtain ⟨n, z, hz⟩ := Concrete.isColimit_exists_rep (D ⋙ E) hc y
    refine ⟨n.obj.val, n.property, ?_⟩
    have hx : E.map (kernel.ι (n.obj.val • 𝟙 F)) z = x := by
      rw [← hcomp n]
      change E.map φ (E.map (colimit.ι D n) z) = x
      change E.map (colimit.ι D n) z = y at hz
      rw [hz, hy]
    rw [← hx]
    have hzero := E.congr_map (kernel.condition (n.obj.val • 𝟙 F))
    rw [E.map_comp, E.map_nsmul, E.map_id, E.map_zero] at hzero
    exact congrArg (fun f ↦ f z) hzero
  · intro h
    have hepi : Epi (E.map φ) := by
      apply (AddCommGrpCat.epi_iff_surjective _).mpr
      intro x
      obtain ⟨n, hn, hx⟩ := h x
      let e := PreservesKernel.iso E (n • 𝟙 F) ≪≫
        AddCommGrpCat.kernelIsoKer (E.map (n • 𝟙 F))
      have hx' : E.map (n • 𝟙 F) x = 0 := by
        simpa [E.map_nsmul, E.map_id] using hx
      let y := e.inv ⟨x, hx'⟩
      have hy : E.map (kernel.ι (n • 𝟙 F)) y = x := by
        change (e.inv ≫ E.map (kernel.ι (n • 𝟙 F))) ⟨x, hx'⟩ = x
        rw [Iso.trans_inv, Category.assoc, PreservesKernel.iso_inv_ι,
          AddCommGrpCat.kernelIsoKer_inv_comp_ι]
        rfl
      let i : ObjectProperty.FullSubcategory
          (fun n : PNat.DvdOrder ↦ n.val ∈ Etale.invertibleTorsionOrders K) :=
        ⟨⟨n, hn.1⟩, hn⟩
      refine ⟨E.map (colimit.ι D i) y, ?_⟩
      change (E.map (colimit.ι D i) ≫ E.map φ) y = x
      rw [hcomp]
      exact hy
    exact isIso_of_mono_of_epi (E.map φ)

/-- A torsion abelian etale sheaf has orders invertible in `K` if and only if the canonical
map from the colimit of its invertible-order torsion subsheaves is an isomorphism.
Source: blueprint `sec-smooth-purity/sk-prop-sf-kunneth-ordinary/`
`lem-kun-invertible-orders-colimit.md` (blueprint: lem-kun-invertible-orders-colimit).

Proof plan:
1. The unrestricted torsion colimit is `F` by `lemma-weil-pbc-torsion-filtered-union`.
   For the restricted diagram, 1 is an index and the product of two indices is a common
   upper bound, so divisibility makes the index filtered. Kernel inclusions yield precisely
   `fieldInvertibleTorsionComparison K F` by the colimit universal property.
2. Exact geometric stalks (`prop-weil-pbc-geometric-stalks-exact`) identify the stalk of
   `F[n]` with the subgroup of the stalk of `F` killed by n. These identifications respect
   the transition maps, since both inclusions into the stalk of `F` send x to x.
3. The colimit of these subgroups is their union: define a compatible homomorphism on an
   element in G[n] using its value there; the common upper bound nm makes the value
   independent of n and proves additivity. Its map into G is the union inclusion, an
   isomorphism exactly when every element is killed by some allowed n.
4. `lem-kun-stalks-commute-colimits` identifies the stalk of the canonical comparison
   with this union inclusion, by its composites with the colimit coprojections.
5. `lemma-weil-pbc-geometric-stalk-conservative` detects its invertibility at every
   geometric point. The resulting condition is exactly
   `Etale.IsTorsionOfInvertibleOrder K (Over.mk (T ↘ Spec (.of K))) F`.
   This gives both implications, with the assumed local torsion of `F`. -/
theorem isTorsionEtaleSheafOfFieldInvertibleOrder_iff_isIso_comparison
    (K : Type u) [Field K] {T : Scheme.{u}} [T.Over (Spec (.of K))]
    (F : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) (hF : F.IsTorsion) :
    Etale.IsTorsionOfInvertibleOrder K (Over.mk (T ↘ Spec (.of K))) F ↔
      IsIso (fieldInvertibleTorsionComparison K F) := by
  have : AB5OfSize.{u, u} AddCommGrpCat.{u + 1} :=
    AB5OfSize_shrink.{u, u, u + 1, u + 1} _
  have _ := hF
  constructor
  · intro h
    apply isIso_of_isIso_sheafFiber_map
    intro t
    let E := (pointSmallEtale (T.algClosurePoint t)).sheafFiber
      (A := AddCommGrpCat.{u + 1})
    have : E.Additive := Functor.additive_of_preserves_binary_products E
    have hE : IsIso (E.map (fieldInvertibleTorsionComparison K F)) :=
      (invertibleTorsion_map_iff K F E).mpr (h _ (T.algClosurePoint t))
    let e := GrothendieckTopology.Point.uliftSheafFiberIso.{u + 1}
      (pointSmallEtale (T.algClosurePoint t)) AddCommGrpCat.{u + 1}
    exact (NatIso.isIso_map_iff e (fieldInvertibleTorsionComparison K F)).mpr hE
  · intro h Ω _ _ s
    let E := (pointSmallEtale s).sheafFiber (A := AddCommGrpCat.{u + 1})
    have : E.Additive := Functor.additive_of_preserves_binary_products E
    exact (invertibleTorsion_map_iff K F E).mp (by infer_instance)

end AlgebraicGeometry.Scheme
