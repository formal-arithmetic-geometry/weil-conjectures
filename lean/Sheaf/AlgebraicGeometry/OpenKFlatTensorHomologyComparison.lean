/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R2
-/
module

public import Sheaf.Algebra.Homology.KFlat
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Homology.Single
public import Mathlib.Topology.Sheaves.Abelian
import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorClosed

/-! # Open restriction and comparison of K-flat tensor homology

Source: Stacks Project, Tags 06YH, 08CG and 06YB.
(blueprint: lem-pc-open-kflat-tensor-homology-comparison).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory

set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

namespace CochainComplex

/-- Open restriction preserves zero maps, since its maps are sectionwise restrictions. -/
instance openRestrictionPreservesZero
    {X : TopCat.{u}} (A : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    (U : TopologicalSpace.Opens X) :
    (SheafOfModules.overFunctor.{u} A U).PreservesZeroMorphisms := by
  constructor
  intro M N
  ext W x
  rfl

/-- The additive tensor structure on the localized site, used in totalization. -/
noncomputable local instance openTensorPreadditive
    {X : TopCat.{u}} (R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})
    (U : TopologicalSpace.Opens X) :
    letI := SheafOfModules.monoidalCategory (R.over U)
    MonoidalPreadditive (SheafOfModules.{u} ((sheafCompose
      ((Opens.grothendieckTopology X).over U)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj (R.over U))) :=
  Classical.choice (SheafOfModules.tensorClosed (R.over U)).1

/-- A roof identifying a local K-flat complex T with the restriction of Q identifies
its tensor homology with the open restriction of the tensor homology of any global
K-flat resolution P of Q. Source: Stacks Project, Tags 06YH, 08CG and 06YB.

Proof: open restriction is exact and commutes with the sheaf tensor and arbitrary
coproducts, hence with total tensor and homology. It preserves K-flatness, so the
restriction of P is a K-flat resolution of the restriction of Q. The roof s,t
identifies that restriction with T in the derived category. Choose a common K-flat
resolution of the roof complex H. Its composites with s and t are quasi-isomorphisms
and comparison with P gives a zigzag of quasi-isomorphisms of K-flat complexes.
To see why a quasi-isomorphism between K-flat complexes remains a quasi-isomorphism
after tensoring with the arbitrary sheaf F restricted to U, first take a K-flat
resolution B of that sheaf in degree zero. Tensoring the map with B preserves
quasi-isomorphisms by the acyclic-cone criterion and symmetry. Tensoring B to F[0]
with either K-flat endpoint also preserves quasi-isomorphisms. The resulting
commutative square and two-of-three prove the claim for F[0]. Taking homology of
the zigzag gives an isomorphism to the tensor with T. Compose it with the open
restriction homology and total-tensor comparisons. The construction is valid for
unbounded complexes,
empty opens, and arbitrary coefficient sheaves; it needs no degree bounds.
(blueprint: lem-pc-open-kflat-tensor-homology-comparison). -/
theorem open_kFlat_tensor_homology_comparison
    {X : TopCat.{u}} (R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})
    (U : TopologicalSpace.Opens X)
    (P Q : CochainComplex (SheafOfModules.{u} ((sheafCompose
      (Opens.grothendieckTopology X)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ)
    (hP : IsKFlat (R := R) P) (q : P ⟶ Q) (hq : QuasiIso q)
    (T H : CochainComplex (SheafOfModules.{u} ((sheafCompose ((Opens.grothendieckTopology X).over U)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj (R.over U))) ℤ)
    (hT : IsKFlat (R := R.over U) T)
    (s : H ⟶ ((SheafOfModules.overFunctor.{u} ((sheafCompose
      (Opens.grothendieckTopology X)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj R) U).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj Q) (t : H ⟶ T) (hs : QuasiIso s) (ht : QuasiIso t)
    (F : SheafOfModules.{u} ((sheafCompose
      (Opens.grothendieckTopology X)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) (i : ℤ) :
    Nonempty (((SheafOfModules.overFunctor.{u} ((sheafCompose
      (Opens.grothendieckTopology X)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj R) U).obj
      ((mapBifunctor P ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj F)
        (@curriedTensor _ _ (SheafOfModules.monoidalCategory R))).homology i)) ≅
      ((mapBifunctor T ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
        ((SheafOfModules.overFunctor.{u} ((sheafCompose
      (Opens.grothendieckTopology X)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj R) U).obj F))
        (@curriedTensor _ _ (SheafOfModules.monoidalCategory (R.over U)))).homology i)) := by sorry

end CochainComplex
