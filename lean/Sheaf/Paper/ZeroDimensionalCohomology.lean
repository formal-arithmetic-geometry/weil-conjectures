/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N1
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.Topology.KrullDimension

/-! # Étale cohomology in dimension zero

Source: literature/blueprint/master/blueprint/sec-curve-estimates/sk-prop-cd/
lem-weil-pbc-zero-dimensional-cohomology.md
(blueprint: lem-weil-pbc-zero-dimensional-cohomology).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

namespace AlgebraicGeometry

/-- Étale cohomology of a separated finite-type zero-dimensional scheme over an
algebraically closed field is the finite product of geometric stalks in degree zero
and vanishes in positive degrees.

Source: literature/blueprint/master/blueprint/sec-curve-estimates/sk-prop-cd/
lem-weil-pbc-zero-dimensional-cohomology.md, node lem-weil-pbc-zero-dimensional-cohomology,
order 1002; Stacks Project, Tags 03QT, 03QU, 03SI and 0A5B
(blueprint: lem-weil-pbc-zero-dimensional-cohomology).
Proof:
1. `lem-weil-pbc-finite-type-dim-zero-artinian` makes the underlying space finite,
   discrete, and closed-point-only. By `lem-weil-pbc-reduction-universal-homeomorphism`,
   the reduction has the same space and is reduced. It is finite type as a closed
   subscheme of C. `lem-weil-pbc-closed-point-residue-field-base` identifies each residue
   field with k. Each singleton is open and closed, and is affine by
   `lem-weil-pbc-finite-discrete-scheme-affine`. Its reduced coordinate ring has one
   prime, so is a field, and the residue-field identification identifies it with k.
   `lem-weil-pbc-scheme-coproduct-family` supplies the map from these point summands to
   the reduction. Their open immersions are disjoint and cover it, so the map is a
   bijective local isomorphism, hence an isomorphism.
2. Apply `lem-weil-pbc-finite-geometric-point-coproduct-cohomology` to this finite
   coproduct: positive cohomology vanishes and degree zero is the product of stalks.
   `thm-weil-pbc-universal-homeomorphism-invariance` transports cohomology from the
   reduction to C. The corresponding geometric points have the same stalks by
   `lem-weil-pbc-inverse-image-stalk-germ`, compatibly with the canonical germ maps.
   Thus the degree-zero map below is invertible. It is the canonical
   derived-to-underived comparison followed by evaluation at the terminal étale object
   and the product of stalk germs. Finiteness follows from step 1. Geometric points
   may have arbitrary algebraically closed coefficient fields.
-/
theorem zero_dimensional_etale_cohomology
    (k : Type u) [Field k] [IsAlgClosed k]
    (C : Scheme.{u}) (f : C ⟶ Spec (.of k))
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (hdim : topologicalKrullDim C ≤ 0)
    (F : Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1})
    (Ω : C → Type u) [∀ x, Field (Ω x)] [∀ x, IsAlgClosed (Ω x)]
    (s : ∀ x : C, Spec (.of (Ω x)) ⟶ C)
    (hs : ∀ x : C, (s x).base.hom default = x) :
    Finite C ∧
    (∀ q : ℕ, 0 < q → Subsingleton
      ((Etale.cohomology AddCommGrpCat.{u + 1} C q).obj
        ((DerivedCategory.singleFunctor
          (Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj F))) ∧
      IsIso
        ((Functor.homologyRightDerivedFunctorObjSingleFunctorIso
            (Sheaf.Γ C.smallEtaleTopology AddCommGrpCat.{u + 1}) F 0).hom ≫
          (Functor.rightDerivedZeroIsoSelf
            (Sheaf.Γ C.smallEtaleTopology AddCommGrpCat.{u + 1})).hom.app F ≫
          F.ΓRes (op (Scheme.Etale.mk (𝟙 C))) ≫
          Pi.lift (fun x : C =>
            (Scheme.pointSmallEtale (s x)).toPresheafFiber
              (Scheme.Etale.mk (𝟙 C))
              (Over.homMk (s x) (Category.comp_id (s x))) F.obj)) := by
  sorry

end AlgebraicGeometry
