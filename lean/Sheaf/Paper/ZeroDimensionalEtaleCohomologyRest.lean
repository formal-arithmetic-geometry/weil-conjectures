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

/-! # Zero-dimensional étale cohomology: cohomological remainder

Source: literature/blueprint/master/blueprint/sec-curve-estimates/sk-prop-cd/
lem-weil-pbc-zero-dimensional-cohomology.md, both proof paragraphs.
(blueprint: zero-dimensional-etale-cohomology-rest).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

namespace AlgebraicGeometry

/-- Positive étale cohomology is zero, and the canonical degree-zero comparison
followed by the product of the chosen geometric stalk germs is invertible.

Source: literature/blueprint/master/blueprint/sec-curve-estimates/sk-prop-cd/
lem-weil-pbc-zero-dimensional-cohomology.md, both proof paragraphs;
Stacks Project, Tags 00KH, 00FV, 054M, 03QT, 03QU, 03SI and 03Q1.
(blueprint: zero-dimensional-etale-cohomology-rest).

Proof:
1. `lem-weil-pbc-finite-type-dim-zero-artinian` gives a finite discrete space of
   closed points. `lem-weil-pbc-reduction-universal-homeomorphism` gives the reduced
   scheme with the same space. It is finite type, being a closed subscheme of C.
   `lem-weil-pbc-closed-point-residue-field-base` identifies its residue fields with k.
   Each singleton is open and closed and affine by
   `lem-weil-pbc-finite-discrete-scheme-affine`. Its reduced coordinate ring has one
   prime, hence is a field, identified with k by its residue field. The inclusions
   induce a map from the coproduct supplied by `lem-weil-pbc-scheme-coproduct-family`.
   Disjoint open summands cover the reduction, so this bijective local isomorphism
   is an isomorphism with the finite coproduct of Spec k.
2. `lem-weil-pbc-finite-geometric-point-coproduct-cohomology` computes the cohomology
   of the pulled-back sheaf there: positive degrees are zero and the canonical
   degree-zero germ map is an isomorphism. Each chosen `s x` factors through the
   reduction since its source is reduced. On a Spec k summand, taking the stalk at
   any algebraically closed geometric field gives the same exact evaluation functor
   (Stacks 03QT and 03QU); no algebraicity or k-linearity of `s x` is required.
3. `thm-weil-pbc-universal-homeomorphism-invariance` transports this calculation to C.
   `lem-weil-pbc-inverse-image-stalk-germ` identifies the pulled-back stalks with those
   of F, preserving germs of sections. Consequently the transported degree-zero map
   is the displayed derived-to-underived comparison, restriction to the identity
   étale object, and product of germs, rather than merely some isomorphism.
   A zero abelian group is subsingleton, giving the other conjunct.
-/
theorem zero_dimensional_etale_cohomology_rest
    (k : Type u) [Field k] [IsAlgClosed k] (C : Scheme.{u})
    (f : C ⟶ Spec (.of k)) [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] (hdim : topologicalKrullDim C ≤ 0)
    (F : Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1})
    (Ω : C → Type u) [∀ x, Field (Ω x)] [∀ x, IsAlgClosed (Ω x)]
    (s : ∀ x : C, Spec (.of (Ω x)) ⟶ C)
    (hs : ∀ x : C, (s x).base.hom default = x) :
    (∀ q : ℕ, 0 < q → Subsingleton
      ((Etale.cohomology AddCommGrpCat.{u + 1} C q).obj
        ((DerivedCategory.singleFunctor
          (Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj F))) ∧
      IsIso ((Functor.homologyRightDerivedFunctorObjSingleFunctorIso
        (Sheaf.Γ C.smallEtaleTopology AddCommGrpCat.{u + 1}) F 0).hom ≫
          (Functor.rightDerivedZeroIsoSelf
            (Sheaf.Γ C.smallEtaleTopology AddCommGrpCat.{u + 1})).hom.app F ≫
          F.ΓRes (op (Scheme.Etale.mk (𝟙 C))) ≫ Pi.lift (fun x : C =>
            (Scheme.pointSmallEtale (s x)).toPresheafFiber
              (Scheme.Etale.mk (𝟙 C))
              (Over.homMk (s x) (Category.comp_id (s x))) F.obj)) := by
  sorry

end AlgebraicGeometry
