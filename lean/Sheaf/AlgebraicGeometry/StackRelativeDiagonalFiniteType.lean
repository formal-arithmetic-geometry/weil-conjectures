/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group O2
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicModuliStack
public import Sheaf.AlgebraicGeometry.DmStackMorphismProperties
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers

/-! # Relative diagonals of algebraic-stack morphisms

Source: Stacks Project, Morphisms of Algebraic Stacks, Tag 04XS
(lemma-properties-diagonal), parts (1) and (2), and its scheme-test proof
(blueprint: lem-sfb-stack-relative-diagonal-finite-type).

The existing relative diagonal sends `x` to `(x,x,id)`. The conclusion uses the
existing algebraic-space test: each scheme 2-base change has an algebraic-space
presentation over the test scheme, and every étale scheme chart of that space
is locally of finite type over the test scheme.
-/

@[expose] public section

set_option autoImplicit false

universe u v₁ w₁ v₂ w₂

open AlgebraicGeometry

namespace CategoryTheory

/-- The relative diagonal of any algebraic-stack morphism is representable by
algebraic spaces and locally of finite type, including its explicit scheme tests.
Source: Stacks Project, Morphisms of Algebraic Stacks, Tag 04XS, parts (1) and (2),
and equation-diagonal, Tag 04XT
(blueprint: lem-sfb-stack-relative-diagonal-finite-type).

Proof:
1. For a scheme test `t = (x,x',α)`, form the algebraic spaces
   `I = Isom_X(x,x')` and `J = Isom_Y(f(x),f(x'))`. The space `I` is locally
   of finite type over `T` by lem-sfb-stack-isom-space-locally-finite-type.
   Applying `f` gives `q : I → J`, and `α` gives a section `a : T → J`.
2. The fibre product `P = T ×_J I` is an algebraic space by
   lem-trf-space-fibre-products-etale-covers. Identify it over `T` with the
   diagonal test: a triple `(z,u:z ≅ x,v:z ≅ x')` satisfying `f(v)=α f(u)`
   maps to `v u⁻¹`. Conversely, an isomorphism `β` with `f(β)=α` maps to
   `(x,id,β)`. Between two triples over the same `β` there is exactly one
   arrow, namely `(u')⁻¹u`; these constructions commute with restriction.
3. The composite `I → J → T` is locally of finite type, so `q` is locally
   of finite type by lem-sfb-space-lft-cancellation, with no hypothesis on
   `J → T`.
4. The projection `P → T` is the base change of `q` along `a`, hence locally
   of finite type by lem-sfb-stack-finite-type-calculus. The equivalence in
   step 2 retains this projection, giving every scheme test and its étale
   chart property. These tests give representability and local finite type. -/
theorem moduliRelativeDiagonal_locallyOfFiniteType {S : Scheme.{u}}
    {X : BasedCategory.{v₁, w₁} (Over S)} {Y : BasedCategory.{v₂, w₂} (Over S)}
    (f : BasedFunctor X Y) (hX : IsAlgebraicModuliStack X)
    (hY : IsAlgebraicModuliStack Y) :
    ModuliSpaceTest @LocallyOfFiniteType (moduliRelativeDiagonal f) := by
  sorry

end CategoryTheory
