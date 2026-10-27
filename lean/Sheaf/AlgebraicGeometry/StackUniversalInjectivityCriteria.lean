/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group O4
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids
public import Sheaf.AlgebraicGeometry.AlgebraicModuliStack
public import Sheaf.AlgebraicGeometry.DmStackMorphismProperties
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.RingTheory.Spectrum.Maximal.Basic

/-! # Universal injectivity of algebraic-stack morphisms

Source: Stacks Project, Morphisms of Stacks, Tag 0CPN, and
`definition-universally-injective`
(blueprint: lem-sfb-stack-universal-injectivity-criteria).

The field-class point maps and relative diagonal are the existing constructions.
The first criterion spells out universal injectivity on arbitrary algebraic-stack
base changes; the third lifts the specified isomorphism, without uniqueness.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open AlgebraicGeometry

namespace CategoryTheory

/-- Universal injectivity, surjectivity of the relative diagonal, and fullness on
geometric fibre groupoids are equivalent.
Source: Stacks Project, Morphisms of Stacks, Tag 0CPN
(blueprint: lem-sfb-stack-universal-injectivity-criteria).

Proof: The fibre product has objects `(x₁,x₂,β)` and pairs of arrows satisfying
`f(v) β = β' f(u)` (lem-sfb-algebraic-stack-fibre-products and
 def-sfb-stable-pointed-moduli-groupoids). Its diagonal sends `x` to `(x,x,id)`.
(1) implies (2): the first projection is a base change of `f`, hence injective on
points. Its section is the diagonal, so the diagonal is surjective.
(2) implies (1): the diagonal is representable, and representable point-surjectivity
is preserved by base change (lem-sfb-stack-relative-diagonal-finite-type,
lem-sfb-representable-stack-point-surjectivity, and
lem-sfb-stack-chartwise-smooth-etale-calculus). The relative diagonal of each base
change is the corresponding pullback. Two points with equal images admit common
field representatives and an isomorphism between their images; these give a point
of the self fibre product (lem-sfb-stack-point-topology). Diagonal surjectivity
makes their two projections equal, proving injectivity after every base change.
(3) implies (2): extend the field of a representative `(x₁,x₂,β)` to its algebraic
closure (def-weil-algebraic-closure). A lift `α` of `β` gives the arrow `(id,α)`
from the diagonal object to this representative, hence the same point class.
(2) implies (3): the diagonal fibre over `(x₁,x₂,β)` is a nonempty algebraic space
locally of finite type over the algebraically closed field, by the relative-diagonal
and representable-surjectivity lemmas. Take an étale scheme chart and a nonempty
affine finite-type open. A maximal ideal exists
(lem-weil-common-extension-fields-maximal-ideal); its residue field is the base field
(lem-weil-pbc-closed-point-residue-field-base). The field-point classification
(lem-weil-pbc-morphism-from-spec-field) gives a rational point of the diagonal fibre.
Unpacking it gives arrows `u : x ≅ x₁`, `v : x ≅ x₂` with `f(v) = β f(u)`.
Then `α = v u⁻¹` is the requested lift. No uniqueness is claimed. -/
theorem stack_universalInjectivity_criteria {S : Scheme.{u}}
    {X Y : BasedCategory.{max u v, max (u + 1) w} (Over S)}
    (f : BasedFunctor X Y) (hX : IsAlgebraicModuliStack X)
    (hY : IsAlgebraicModuliStack Y) :
    ((∀ (Z : BasedCategory.{max u v, max (u + 1) w} (Over S)),
        IsAlgebraicModuliStack Z → ∀ g : BasedFunctor Z Y,
          Function.Injective (moduliPointMap (moduliTwoFiberFst g f))) ↔
      Function.Surjective (moduliPointMap (moduliRelativeDiagonal f))) ∧
    (Function.Surjective (moduliPointMap (moduliRelativeDiagonal f)) ↔
      ∀ (K : Type u) [Field K] [IsAlgClosed K] (a : Spec (.of K) ⟶ S)
        (x₁ x₂ : Functor.Fiber X.p (Over.mk a))
        (β : (moduliFiberMap f (Over.mk a)).obj x₁ ≅
          (moduliFiberMap f (Over.mk a)).obj x₂),
        ∃ α : x₁ ≅ x₂, (moduliFiberMap f (Over.mk a)).mapIso α = β) := by
  sorry

end CategoryTheory
