/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NK
-/
module

public import Sheaf.AlgebraicGeometry.InvertibleTorsionOrders
public import Sheaf.AlgebraicGeometry.TorsionEtaleSheaf
public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Sites.Abelian
import WeilConjectures.AlgebraicGeometry.GeometricStalkColimits
import Mathlib.Algebra.Homology.Additive
import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Sheaf.AlgebraicGeometry.TorsionFilteredUnion
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Mathlib.CategoryTheory.Sites.Point.Skyscraper
import Sheaf.AlgebraicGeometry.PointedEtaleStalk

/-!
# The colimit description of invertible orders

Source: blueprint `sec-smooth-purity/sk-prop-sf-kunneth-ordinary/`
`lem-kun-invertible-orders-colimit.md` (blueprint: lem-kun-invertible-orders-colimit).

The diagram, its cocone of kernel inclusions, and the induced comparison are explicit.
The index inherits divisibility from `PositiveNat`; no bounded exponent is imposed.
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
      (fun n : PositiveNat ↦ n.val ∈ Etale.invertibleTorsionOrders K) ⥤
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
  sorry

end AlgebraicGeometry.Scheme
