/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q37
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids
public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.AlgebraicModuliStack
public import Sheaf.AlgebraicGeometry.DmStackMorphismProperties
public import Sheaf.AlgebraicGeometry.StackPointTopologyFlatLfpOpen
import Sheaf.AlgebraicGeometry.StackChartwiseSmoothEtaleCalculus

/-! # Finite-type points meet locally closed subsets of algebraic stacks

Source: Stacks Project, stacks-morphisms.tex, Tags 06G2, 06FY and 06FX
(blueprint: lem-sfb-stack-locally-closed-finite-type-point).

The finite-type point set uses actual locally finite type field representatives, the
existing point quotient, and the topology defined by smooth surjective scheme atlases.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w

open AlgebraicGeometry

namespace CategoryTheory

/-- Points having a locally finite type field representative. A field spectrum has one
scheme point, so the range below is exactly the class of the displayed representative.
The chartwise test includes algebraic-space representability and uses local finite type
on every etale scheme chart of every scheme base change. For algebraic stacks this is
also the smooth-chart definition, by locality of local finite type.
Source: Stacks Project, Tag 06FY, definition-finite-type-point, and Tag 06FX, condition (1)
(blueprint: lem-sfb-stack-locally-closed-finite-type-point). -/
def finiteTypeModuliPoints {S : Scheme.{u}} (F : BasedCategory.{v, w} (Over S)) :
    Set (ModuliPoints F) :=
  {x | ∃ (K : Type u) (_ : Field K) (b : Spec (.of K) ⟶ S)
      (a : BasedFunctor (discreteModuli (yoneda.obj (Over.mk b))) F),
    ModuliSpaceTest @LocallyOfFiniteType a ∧ x ∈ Set.range (moduliSchemePointMap a)}

/-- Every nonempty locally closed subset of an algebraic stack contains a finite-type
point. There are no Jacobson, Noetherian or quasi-compactness assumptions.
Source: Stacks Project, Tag 06G2, lemma-enough-finite-type-points, first assertion
(blueprint: lem-sfb-stack-locally-closed-finite-type-point).

Proof:
1. Choose a smooth surjective scheme atlas p:U → F. Pull back Z along its point map.
The atlas topology and continuity from lem-sfb-stack-point-topology-flat-lfp-open make
this inverse image locally closed in U. It is nonempty: the field-extension lifting
criterion of lem-sfb-stack-chartwise-smooth-etale-calculus lifts a representative of
any point of Z to U after extending its field, without changing its point class.
2. Apply lem-sfb-finite-type-points-detect-open to this nonempty locally closed subset
of the arbitrary scheme U. It supplies u whose residue-field morphism a:Spec κ(u) → U
is of finite type, hence locally of finite type by def-weil-finite-type-morphism.
3. The atlas p is smooth, hence locally of finite presentation and locally of finite
type, by lem-sfb-stack-chartwise-smooth-etale-calculus. Its composition with a is locally
of finite type by the composition clause of the same calculus. This is a field
representative of the image of u, which lies in Z by construction. The point-map
composition rule from lem-sfb-stack-point-topology-flat-lfp-open identifies its class
with that image, proving the required nonempty intersection.
-/
theorem stack_locallyClosed_inter_finiteTypePoints_nonempty {S : Scheme.{u}}
    (F : BasedCategory.{v, w} (Over S)) (hF : IsAlgebraicModuliStack F)
    (Z : Set (ModuliPoints F)) (hZ : IsLocallyClosed Z) (hne : Z.Nonempty) :
    (Z ∩ finiteTypeModuliPoints F).Nonempty := by
  sorry

end CategoryTheory
