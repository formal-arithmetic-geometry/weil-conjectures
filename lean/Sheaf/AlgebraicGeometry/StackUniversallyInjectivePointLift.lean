/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q110
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids
public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.AlgebraicModuliStack
public import Sheaf.AlgebraicGeometry.DmStackMorphismProperties
import Sheaf.AlgebraicGeometry.AlgebraicStackFibreProducts
import Sheaf.AlgebraicGeometry.StackChartwiseSmoothEtaleCalculus
import Sheaf.AlgebraicGeometry.StackUniversalInjectivityCriteria
import Sheaf.AlgebraicGeometry.SpaceTwoFieldScalarAlgebraicity
import WeilConjectures.RingTheory.TensorFiniteTypeLimit
import WeilConjectures.FieldTheory.AlgClosedFiniteTypeTensorDomain
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.LinearAlgebra.TensorProduct.Defs
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! # Same-field lifting for universally injective algebraic-stack morphisms

Source: Stacks Project, Morphisms of Stacks, Tag 0DTM,
lemma-universally-injective-point
(blueprint: lem-sfb-stack-universally-injective-point-lift).

The point class is the existing quotient of field-valued objects. The conclusion retains
an object and an isomorphism in the fibre over the original field scheme.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open AlgebraicGeometry

namespace CategoryTheory

/-- The underlying point class of an object in the fibre over a specified field scheme.
The equality defining the fibre gives the required field-scheme isomorphism directly.
Source: Stacks Project, Tag 0DTM, the underlying point of the given field-valued object
(blueprint: lem-sfb-stack-universally-injective-point-lift). -/
def moduliFieldFiberPoint {S : Scheme.{u}} {F : BasedCategory.{v, w} (Over S)}
    {K : Type u} [Field K] (a : Spec (.of K) ⟶ S)
    (x : Functor.Fiber F.p (Over.mk a)) : ModuliPoints F :=
  Quot.mk (ModuliFieldRelation F)
    ⟨x.val, ⟨K, inferInstance, ⟨(Over.forget S).mapIso (eqToIso x.property)⟩⟩⟩

/-- A geometric object in the point image of a universally injective map lifts over
its original algebraically closed field, with an isomorphism to its specified image.
Source: Stacks Project, Morphisms of Stacks, Tag 0DTM
(blueprint: lem-sfb-stack-universally-injective-point-lift).

Proof:
1. Form P = X ×_Y Spec K using lem-sfb-algebraic-stack-fibre-products and the
   triple construction of def-sfb-stable-pointed-moduli-groupoids. The image hypothesis
   gives a field object of P after a common extension, so P is nonempty. Universal
   injectivity is preserved by this base change. A K-object of P gives the desired lift.
2. Apply lem-sfb-stack-locally-closed-finite-type-point to the whole nonempty point
   space of P to obtain Spec L → P locally of finite type, where L extends K.
   It is representable by lem-sfb-stack-diagonal-space-source-representability.
3. Put R = Spec L ×_P Spec L. Both projections to Spec L are locally of finite type
   by lem-sfb-stack-chartwise-smooth-etale-calculus. Universal injectivity makes the
   relative diagonal surjective by lem-sfb-stack-universal-injectivity-criteria.
   That diagonal is representable, so lem-sfb-representable-stack-point-surjectivity
   makes R → Spec L ×_K Spec L surjective.
4. Identify the target with Spec B, B = L ⊗_K L, by the tensor pushout property
   lem-weil-pbc-algebra-tensor-pushout-universal-property. Multiplication B → L makes
   B nonzero. A nonzero zero-divisor in B would descend to finitely generated K-subalgebras
   R', S' of L by lem-weil-pbc-tensor-finite-type-limit. These are domains, so
   lem-weil-pbc-algclosed-finite-type-tensor-domain rules it out. Thus B is a domain.
   Lift its zero prime to a field-valued point of R; the resulting B → F is injective.
   Apply lem-sfb-space-two-field-scalar-algebraicity to the two projections of R:
   the image of every λ ⊗ 1 is algebraic over the image of 1 ⊗ L in F.
5. Injectivity gives a nontrivial relation ∑ λ^i ⊗ b_i = 0 in B. If λ were
   transcendental over K, its finitely many powers would be linearly independent.
   Extend them to a basis by lem-weil-pbc-vector-space-basis-through-vector; apply each
   coordinate functional tensored with id, using def-weil-pbc-module-tensor-product.
   This forces every b_i to vanish, a contradiction. Hence L/K is algebraic.
6. Since K is algebraically closed (def-weil-algebraic-closure), every element of L
   lies in the image of K: a nonzero polynomial annihilating it splits into linear
   factors. The structural embedding K → L is therefore an isomorphism. Transport the
   L-object along its inverse to a K-object of P. Projecting its triple gives x and
   the isomorphism f(x) ≅ y over Spec K, as required. -/
theorem stack_universallyInjective_point_lift {S : Scheme.{u}}
    {X Y : BasedCategory.{max u v, max (u + 1) w} (Over S)}
    (f : BasedFunctor X Y) (hX : IsAlgebraicModuliStack X)
    (hY : IsAlgebraicModuliStack Y)
    (hf : ∀ (Z : BasedCategory.{max u v, max (u + 1) w} (Over S)),
      IsAlgebraicModuliStack Z → ∀ g : BasedFunctor Z Y,
        Function.Injective (moduliPointMap (moduliTwoFiberFst g f)))
    (K : Type u) [Field K] [IsAlgClosed K] (a : Spec (.of K) ⟶ S)
    (y : Functor.Fiber Y.p (Over.mk a))
    (hy : moduliFieldFiberPoint a y ∈ Set.range (moduliPointMap f)) :
    ∃ x : Functor.Fiber X.p (Over.mk a),
      Nonempty ((moduliFiberMap f (Over.mk a)).obj x ≅ y) := by
  sorry

end CategoryTheory
