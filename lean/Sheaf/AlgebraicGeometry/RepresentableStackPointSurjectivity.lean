/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NC
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids
public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.AlgebraicSpacePointClasses
public import Sheaf.AlgebraicGeometry.AlgebraicModuliStack
public import Sheaf.AlgebraicGeometry.StackPointTopologyFlatLfpOpen

/-! # Surjectivity on points of representable stack morphisms

Source: Stacks Project, stacks-properties.tex, Tag 04XI (lemma-characterize-surjective),
and algebraic.tex, Tag 03YS (lemma-representable-algebraic), part (2)
(blueprint: lem-sfb-representable-stack-point-surjectivity).

The two statements cover algebraic-stack and algebraic-space sources, respectively.
Every algebraic-space presentation of each actual scheme base change is tested, using
its specified projection and the existing field-valued point classes.
-/

@[expose] public section

set_option autoImplicit false

universe u v₁ w₁ v₂ w₂

open AlgebraicGeometry

namespace CategoryTheory

/-- For a morphism of algebraic stacks representable by algebraic spaces, surjectivity
on point classes is equivalent to point-surjectivity of every scheme base change.
Source: Stacks Project, stacks-properties.tex, Tag 04XI, equivalence (1) ⇔ (2)
(blueprint: lem-sfb-representable-stack-point-surjectivity).

Proof: (1) Assume the map on stack points is surjective. For a scheme map t:T → X and
a residue-field representative t₀ of a point of T, choose a field-valued y of Y whose
image has class [t(t₀)]. The common-extension relation of
lem-sfb-stack-point-topology-flat-lfp-open gives a common field M and an isomorphism
f(y_M) ≅ t(t₀,M). The triple (t₀,M, y_M, isomorphism) is an object of the 2-fibre product
of def-sfb-stable-pointed-moduli-groupoids. Through any HasSpaceBaseChange presentation
it gives a point of Z mapping to [t₀], using def-a1-algebraic-space-point-classes.
Thus every displayed projection is surjective on points.
(2) Conversely, represent a point of X by x₀:Spec K → X. Representability supplies
an algebraic-space presentation of Y ×_X Spec K. The projection is point-surjective,
so choose a field-valued representative above the unique point of Spec K. Its triple
consists of a field extension K → M, an object y_M of Y, and f(y_M) ≅ (x₀)_M.
Consequently [y_M] maps to [x₀]. Neither direction uses flatness or finite presentation.
-/
theorem representable_stack_point_surjectivity
    {S : Scheme.{u}}
    (X : BasedCategory.{v₁, w₁} (Over S)) (hX : IsAlgebraicModuliStack X)
    (Y : BasedCategory.{v₂, w₂} (Over S)) (hY : IsAlgebraicModuliStack Y)
    (f : BasedFunctor Y X) (hf : IsRepresentableByAlgebraicSpaces f) :
    Function.Surjective (moduliPointMap f) ↔
      ∀ (T : Over S) (t : BasedFunctor (discreteModuli (yoneda.obj T)) X)
        (Z : AlgebraicSpace S) (p : Z.obj.obj ⟶ yoneda.obj T),
        HasSpaceBaseChange f T t Z p → Function.Surjective (AlgebraicSpace.mapPoint p) := by
  sorry

/-- The same criterion for an algebraic-space source, using its algebraic-space point
classes and its discrete category fibred in sets.
Source: Stacks Project, stacks-properties.tex, Tag 04XI, and algebraic.tex,
Tag 03YS (lemma-representable-algebraic), part (2)
(blueprint: lem-sfb-representable-stack-point-surjectivity).

Proof: (1) Given surjectivity on the point classes of A, represent a point of a scheme
T → X by t₀ over its residue field. A preimage in A and t(t₀) agree over a common
extension M. Their equality in the discrete source and their isomorphism in X give the
2-fibre-product triple of def-sfb-stable-pointed-moduli-groupoids. Any presentation Z
therefore has a point above [t₀], in def-a1-algebraic-space-point-classes.
(2) For x₀:Spec K → X, take an algebraic-space presentation of A ×_X Spec K. Its
point-surjective projection has a field-valued representative over the unique point of
Spec K. The triple gives an A-valued point over a field extension M of K and an
isomorphism of its image with (x₀)_M, hence a preimage of [x₀]. The canonical map
moduliSpacePointMap identifies the existing point classes with those of the discrete
fibred groupoid, as in lem-sfb-stack-point-topology-flat-lfp-open. This is also the
algebraic-stack interpretation of A supplied by Tag 03YS(2). No flatness or finite
presentation is used.
-/
theorem representable_space_stack_point_surjectivity
    {S : Scheme.{u}}
    (X : BasedCategory.{v₁, w₁} (Over S)) (hX : IsAlgebraicModuliStack X)
    (A : AlgebraicSpace S) (f : BasedFunctor (discreteModuli A.obj.obj) X)
    (hf : IsRepresentableByAlgebraicSpaces f) :
    Function.Surjective (moduliPointMap f ∘ moduliSpacePointMap A.obj.obj) ↔
      ∀ (T : Over S) (t : BasedFunctor (discreteModuli (yoneda.obj T)) X)
        (Z : AlgebraicSpace S) (p : Z.obj.obj ⟶ yoneda.obj T),
        HasSpaceBaseChange f T t Z p → Function.Surjective (AlgebraicSpace.mapPoint p) := by
  sorry

end CategoryTheory
