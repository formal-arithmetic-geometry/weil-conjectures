/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q23
-/
module

public import Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids
public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.CategoryTheory.SiteStackification
public import Sheaf.AlgebraicGeometry.AlgebraicModuliStack
public import Sheaf.AlgebraicGeometry.StackChartwiseSmoothEtaleCalculus
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Algebra.Field.Defs
import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-! # An algebraic stack with setoid fibres is an algebraic space

Source: Stacks Project, algebraic.tex, Tag 04SZ
(proposition-algebraic-stack-no-automorphisms), implication (1) to (3)
(blueprint: lem-sfb-algebraic-stack-setoid-space).

The hypotheses retain fppf descent, smoothness on the actual algebraic-space
base changes, and surjectivity by field-extension lifting. The conclusion is an
equivalence over the scheme category, rather than just a pointwise bijection.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open AlgebraicGeometry

namespace CategoryTheory

/-- An fppf stack with algebraic-space diagonal and a representable smooth surjective
scheme atlas is an algebraic space if every fibre is a setoid.
Source: Stacks Project, Tag 04SZ (proposition-algebraic-stack-no-automorphisms),
implication (1) to (3) (blueprint: lem-sfb-algebraic-stack-setoid-space).

Proof:
1. Every étale covering is fppf, by def-weil-etale-morphism and def-pc-fppf-site.
   Thus the assumed descent gives IsModuliStack W. The diagonal and chartwise
   smoothness hypotheses are exactly those of def-sfb-algebraic-moduli-stack.
   Field-extension lifting is equivalent to surjectivity on the scheme charts:
   for a point t of a test scheme T restrict its object to Spec κ(t), lift over
   an extension L, and lift an L-point of the algebraic-space base change to a
   point of an étale scheme chart. Conversely, a point in that chart over a
   field object has a residue field extending the original field and supplies
   the lift and its isomorphism. This uses def-trf-algebraic-space and
   def-weil-field. Hence W satisfies IsAlgebraicModuliStack.
2. For every test scheme T and object x, every automorphism of x equals its
   identity by hsetoid, including when T is nonreduced.
3. Apply lem-sfb-algebraic-setoid-space to obtain an algebraic space E and an
   equivalence from its discrete fibred groupoid to W. Invert that equivalence
   over Sch/S to obtain the displayed direction. The presheaf underlying E has
   value E(T), so discreteModuli E.obj.obj is the required discrete groupoid. -/
theorem algebraicStack_setoid_space
    {S : Scheme.{u}} (W : BasedCategory.{v, w} (Over S))
    (hstack : IsFppfModuliStack W)
    (hdiag : HasAlgebraicSpaceDiagonal W)
    (hatlas : ∃ (U : Over S) (a : BasedFunctor (discreteModuli (yoneda.obj U)) W),
      (∀ (T : Over S) (t : BasedFunctor (discreteModuli (yoneda.obj T)) W),
        ∃ (Z : AlgebraicSpace S) (p : Z.obj.obj ⟶ yoneda.obj T),
          HasSpaceBaseChange a T t Z p ∧ SpaceMapIsSmooth Z T p) ∧
        IsSurjectiveModuliMap a)
    (hsetoid : ∀ (T : Over S) (x y : Functor.Fiber W.p T), Subsingleton (x ⟶ y)) :
    ∃ (E : AlgebraicSpace S) (e : BasedFunctor W (discreteModuli E.obj.obj)),
      e.toFunctor.IsEquivalence := by
  sorry

end CategoryTheory
