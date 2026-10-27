/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NP
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicModuliStack
public import Sheaf.AlgebraicGeometry.RelativeModuliInertia
public import Sheaf.AlgebraicGeometry.DmStackMorphismProperties
import Sheaf.AlgebraicGeometry.RelativeInertiaSecondDiagonalGeometry

/-! # Relative inertia detects locally quasi-finite diagonals

Source: Stacks Project, Morphisms of Stacks, Tag 0CL0, part (5)
(blueprint: lem-sfb-inertia-locally-quasifinite-diagonal).

Local quasi-finiteness is tested on every étale scheme chart of every scheme
2-base change, using the Stacks finite-type convention of `Scheme.Hom.IsLocallyQuasiFinite`.
-/

@[expose] public section

set_option autoImplicit false

universe u v₁ w₁ v₂ w₂

namespace CategoryTheory

/-- The relative inertia projection and relative diagonal are representable by algebraic
spaces, and one is locally quasi-finite exactly when the other is. For the structural
map to the base, the canonical inclusion identifies relative and ordinary inertia.

Source: Stacks Project, Morphisms of Stacks, Tag 0CL0, part (5), with the inertia
constructions of Tags 050Q and 034H
(blueprint: lem-sfb-inertia-locally-quasifinite-diagonal).

Proof:
1. Apply `lem-sfb-relative-inertia-second-diagonal-geometry` for representability
   of both maps and for the absolute specialization, via the canonical inclusion.
2. A scheme test of the diagonal is the sheaf J of isomorphisms φ : a ≅ b with
   f(φ) = α, for a test (a,b,α). Send a fibre triple (z,i,j) to j i⁻¹; the inverse
   sends φ to (a,1,φ). The inertia fibre at b is H = ker(Aut(b) → Aut(f(b))):
   send (x,δ,θ : x ≅ b) to θ δ θ⁻¹, with inverse γ ↦ (b,γ,1).
   These formulas commute with pullback, as in `def-sfb-stable-pointed-moduli-groupoids`.
3. If the diagonal is locally quasi-finite, its test (b,b,1) is H. Thus every
   scheme base change of the inertia projection is locally quasi-finite.
4. Conversely, `lem-sfb-stack-relative-diagonal-finite-type` makes J and H locally
   of finite type over the testing scheme, without a finite-type hypothesis on f.
   The hypothesis makes H locally quasi-finite. Composition and inversion give
   H its group algebraic-space structure, since they preserve the kernel condition.
5. The action (γ,φ) ↦ γφ makes J an H-pseudo-torsor: the map to J × J is
   (γ,φ) ↦ (γφ,φ), with inverse (ψ,φ) ↦ (ψφ⁻¹,φ). The formulas respect the
   equations f(φ) = α and f(γ) = 1, commute with pullback, and cancel inverses.
   No local section is required; J may be empty.
6. Apply `lem-sfb-locally-quasifinite-pseudo-torsor` (Stacks Tag 0DSK(2)) to J
   under H. Every diagonal scheme test is therefore locally quasi-finite, which
   proves the converse on all its étale scheme charts. -/
theorem relative_inertia_locallyQuasiFinite_diagonal {S : AlgebraicGeometry.Scheme.{u}}
    (F : BasedCategory.{v₁, w₁} (Over S)) (G : BasedCategory.{v₂, w₂} (Over S))
    (f : BasedFunctor F G) (hF : IsAlgebraicModuliStack F) (hG : IsAlgebraicModuliStack G) :
    IsRepresentableByAlgebraicSpaces (relativeModuliInertiaProjection f) ∧
    IsRepresentableByAlgebraicSpaces (moduliRelativeDiagonal f) ∧
    (ModuliSpaceTest @AlgebraicGeometry.Scheme.Hom.IsLocallyQuasiFinite
        (relativeModuliInertiaProjection f) ↔
      ModuliSpaceTest @AlgebraicGeometry.Scheme.Hom.IsLocallyQuasiFinite
        (moduliRelativeDiagonal f)) ∧
    (relativeModuliInertiaToAbsolute (moduliBaseStructure F)).toFunctor.IsEquivalence := by
  sorry

end CategoryTheory
