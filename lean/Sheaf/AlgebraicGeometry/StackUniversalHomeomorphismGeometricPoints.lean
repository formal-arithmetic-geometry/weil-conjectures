/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q66
-/
module

public import Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids
public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.AlgebraicModuliStack
public import Sheaf.AlgebraicGeometry.DmStackMorphismProperties
public import Sheaf.AlgebraicGeometry.StackPointTopologyFlatLfpOpen
public import Mathlib.CategoryTheory.Skeletal
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import Sheaf.AlgebraicGeometry.StackUniversalInjectivityCriteria

/-! # Geometric points of a universal homeomorphism from a stack

Source: Stacks Project, Morphisms of Stacks, Tags 0CI7, 0CPN and 0DTM
(blueprint: lem-sfb-stack-universal-homeomorphism-geometric-points).

The hypothesis uses every algebraic-stack base change and the existing atlas topology.
The conclusions use the maps on isomorphism classes induced by the actual fibre functors.
For a discrete algebraic-space fibre its skeleton is canonically its set of sections.
-/

@[expose] public section

set_option autoImplicit false

universe u v w v' w'

open AlgebraicGeometry

namespace CategoryTheory

/-- A universal homeomorphism from a Deligne--Mumford stack to an algebraic space
is bijective on geometric isomorphism classes, also after any algebraic-space base change.
Source: Stacks Project, Morphisms of Stacks, Tags 0CI7, 0CPN and 0DTM
(blueprint: lem-sfb-stack-universal-homeomorphism-geometric-points).

Proof:
1. Every base-changed point map is a homeomorphism, hence injective; thus the map
is universally injective. Its identity base change is also surjective on points.
Composition with the map respects fibre isomorphisms, giving its map on skeletons
(def-sfb-stable-pointed-moduli-groupoids and def-trf-algebraic-space).
2. Given a K-valued point of the target, point-surjectivity puts its field class in
the image. Apply lem-sfb-stack-universally-injective-point-lift, using universal
injectivity from step 1, to lift it over the same algebraically closed field K.
The target fibre is discrete, so the comparison isomorphism is equality. This
proves surjectivity on geometric isomorphism classes.
3. Two K-valued objects with the same image have an isomorphism between their images.
The fullness criterion of lem-sfb-stack-universal-injectivity-criteria lifts this
isomorphism to an isomorphism of the two objects, proving injectivity on classes.
No uniqueness of the lifted isomorphism is asserted.
4. For any algebraic-space map Y1 to Y, objects in the two-fibre product are triples
(a,z,gamma), with gamma identifying q(a) with the image of z. Step 2 supplies a
triple over every z. Step 3 identifies any two triples over the same z: their
compatibility holds because Y(K) is discrete. Hence the projection is bijective
on classes (def-sfb-stable-pointed-moduli-groupoids and def-trf-algebraic-space).
This includes arbitrary base changes, empty fibres and nontrivial stabilizers. -/
theorem stack_universalHomeomorphism_geometricPoints {S : Scheme.{u}}
    (A : BasedCategory.{max u v, max (u + 1) w} (Over S)) (Y : AlgebraicSpace S)
    (q : BasedFunctor A (discreteModuli Y.obj.obj))
    (hA : IsDeligneMumfordModuliStack A)
    (hq : ∀ (Z : BasedCategory.{max u v v', max (u + 1) w w'} (Over S)),
      IsAlgebraicModuliStack Z → ∀ g : BasedFunctor Z (discreteModuli Y.obj.obj),
        IsHomeomorph (moduliPointMap (moduliTwoFiberFst g q))) :
    (∀ (K : Type u) [Field K] [IsAlgClosed K] (a : Spec (.of K) ⟶ S),
      Function.Bijective ((moduliFiberMap q (Over.mk a)).mapSkeleton.obj)) ∧
    (∀ (Y1 : AlgebraicSpace S) (h : Y1 ⟶ Y)
        (K : Type u) [Field K] [IsAlgClosed K] (a : Spec (.of K) ⟶ S),
      Function.Bijective ((moduliFiberMap
        (moduliTwoFiberFst (discreteModuliMap h.hom.hom) q)
        (Over.mk a)).mapSkeleton.obj)) := by
  sorry

end CategoryTheory
