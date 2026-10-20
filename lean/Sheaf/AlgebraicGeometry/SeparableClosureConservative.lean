/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q34
-/
module

public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Sites.Sheaf
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import Mathlib.AlgebraicGeometry.Fiber
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.Topology.InverseImageModule
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Topology.Sheaves.Functors
public import WeilConjectures.AlgebraicGeometry.Picard.Defs
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Sheaf.AlgebraicGeometry.GeometricStalkAsPullback
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageExact
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Sheaf.AlgebraicGeometry.StalkFaithfulDerived

/-!
# Conservativity of base change to a separable closure

Source: blueprint sec-smooth-purity/sk-prop-sf-kunneth-ordinary,
lemma lem-kun-sep-closure-conservative (blueprint: lem-kun-sep-closure-conservative).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Every geometric point lifts to base change by a separable closure, and inverse image
along the projection detects isomorphisms of abelian étale sheaves and of unbounded
derived objects.

Source: blueprint sec-smooth-purity/sk-prop-sf-kunneth-ordinary,
lemma lem-kun-sep-closure-conservative (blueprint: lem-kun-sep-closure-conservative).

Proof:
1. For a geometric point `x : Spec Ω ⟶ X`, the composite with `s` gives `K → Ω`
   (def-weil-geometric-point, def-weil-affine-spectrum). The algebraic extension `L/K`
   (def-kun-separably-closed) embeds in the algebraically closed field `Ω` over this map
   (lem-weil-pbc-algebraic-extension-embeds-algebraically-closed).
2. Applying `Spec` to that embedding and using the fibre-product universal property
   gives a lift of `x` with the same field `Ω` (def-pc-fibre-product, def-pc-base-change).
   No uniqueness or preselected inclusion `L ⊆ Ω` is asserted.
3. If the pullback of a sheaf morphism is invertible, its further pullback to every
   lifted point is invertible. The inverse-image composition comparison
   (lem-weil-pbc-inverse-image-composition) identifies this with the original stalk map
   (lem-kun-stalk-as-pullback). Geometric stalks detect isomorphisms
   (lemma-weil-pbc-geometric-stalk-conservative).
4. Inverse image is exact (prop-weil-pbc-inverse-image-exact). Its derived functor is
   termwise inverse image followed by localization
   (lem-weil-pbc-exact-functor-derived-factorization, def-weil-pbc-derived-inverse-image).
   Apply the sheaf composition comparison degree by degree. Naturality with respect
   to differentials makes it a chain isomorphism. Its localization is natural for chain
   maps and inverses of quasi-isomorphisms, hence on the entire unbounded category.
5. Thus invertibility after derived pullback implies invertibility after pullback to
   every geometric point. Apply lem-kun-stalk-faithful-derived to conclude.
6. Conversely, any functor sends a morphism and its inverse to mutual inverses, proving
   the forward implication in each displayed equivalence. -/
theorem separableClosure_baseChange_conservative
    (K L : Type u) [Field K] [Field L] [Algebra K L] [IsSepClosure K L]
    (X : Scheme.{u}) (s : X ⟶ Spec (.of K)) :
    (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X),
      ∃ y : Spec (.of Ω) ⟶ pullback s (Spec.map (CommRingCat.ofHom (algebraMap K L))),
        y ≫ pullback.fst s (Spec.map (CommRingCat.ofHom (algebraMap K L))) = x) ∧
    (∀ (F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (α : F ⟶ G),
      IsIso α ↔ IsIso ((Etale.upperStar AddCommGrpCat.{u + 1}
        (pullback.fst s (Spec.map (CommRingCat.ofHom (algebraMap K L))))).map α)) ∧
    (∀ (A B : DerivedCategory (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
      (α : A ⟶ B), IsIso α ↔ IsIso
        ((Etale.upperStar AddCommGrpCat.{u + 1}
          (pullback.fst s
            (Spec.map (CommRingCat.ofHom (algebraMap K L))))).mapDerivedCategory.map α)) := by
  sorry

end AlgebraicGeometry
