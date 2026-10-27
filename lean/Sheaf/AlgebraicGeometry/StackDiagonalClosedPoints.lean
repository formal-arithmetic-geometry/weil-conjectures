/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q24
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicModuliStack
public import Sheaf.AlgebraicGeometry.DmStackMorphismProperties
public import Sheaf.AlgebraicGeometry.RelativeModuliInertia
public import Sheaf.AlgebraicGeometry.SchemeStackDiagonalPresentation
public import Sheaf.AlgebraicGeometry.StackPointTopologyFlatLfpOpen
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Sheaf.AlgebraicGeometry.SmoothPresentationClosedSubsets
import Sheaf.AlgebraicGeometry.StackClosedImmersionCalculus
import Sheaf.AlgebraicGeometry.AlgebraicStackFibreProducts
import Mathlib.AlgebraicGeometry.Scheme

/-! # The diagonal of an algebraic stack preserves closed points

Source: Alper, Adequate moduli spaces and geometrically reductive group schemes,
arXiv:1005.2398v3, Theorem 8.3.2, proof of (3) implies (1), printed pp. 39--40
(blueprint: lem-sfb-stack-diagonal-closed-points).

The product is the existing 2-fibre product of structural maps to the base. Its diagonal
is the existing functor sending an object to its identical pair with identity comparison.
Point spaces carry the existing smooth-atlas topology on the quotient of field objects.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open AlgebraicGeometry CategoryTheory.Limits

namespace CategoryTheory

/-- The diagonal of a finite-type algebraic stack over a field, with quasi-finite
separated diagonal, sends closed points to closed points.
Source: Alper, arXiv:1005.2398v3, Theorem 8.3.2, proof of (3) implies (1), pp. 39--40
(blueprint: lem-sfb-stack-diagonal-closed-points).

Proof:
1. For a closed point x, lem-sfb-smooth-presentation-closed-subsets supplies the
   reduced closed substack i : Z → F supported on {x}. By
   lem-sfb-stack-closed-immersion-calculus it is locally of finite type over k.
   The lemma lem-sfb-singleton-stack-finite-field-homeomorphism supplies a finite
   field extension K/k and a universally homeomorphic k-map π : Z → Spec K.
2. By lem-sfb-algebraic-stack-fibre-products the products Z ×_k Z and F ×_k F
   are algebraic stacks. The map j = i × i factors as two base changes of i.
   By lem-sfb-stack-closed-immersion-calculus it is a closed immersion and its
   point map is closed.
3. The map h = π × π factors as two base changes of π through Spec K ×_k Z.
   The universal clause of lem-sfb-singleton-stack-finite-field-homeomorphism
   makes each factor a homeomorphism on points, and hence h is a homeomorphism.
4. The scheme diagonal δ : Spec K → Spec K ×_k Spec K has closed singleton image.
   Indeed def-weil-affine-spectrum identifies it with the spectrum of the
   multiplication map K ⊗_k K → K. This map is onto since a ⊗ 1 maps to a;
   its kernel is maximal, and its vanishing locus is the corresponding singleton.
5. If z is the unique point of Z, naturality gives h Δ_Z = δ π and
   j Δ_Z = Δ_F i. The homeomorphism |h| therefore makes {Δ_Z(z)} closed.
   The closed point map |j| sends it to {Δ_F(x)}, which is consequently closed.
   This proves the assertion for every closed point; the empty stack is vacuous. -/
theorem stack_diagonal_closed_points
    (k : Type u) [Field k]
    (F : BasedCategory.{v, w} (Over (Spec (CommRingCat.of k))))
    (hF : IsAlgebraicModuliStack F)
    (hft : ∃ (U : Over (Spec (CommRingCat.of k)))
      (a : BasedFunctor (discreteModuli (yoneda.obj U)) F),
      IsSmoothModuliAtlas F U a ∧ LocallyOfFiniteType U.hom ∧ QuasiCompact U.hom)
    (hΔ : HasSchemeStackDiagonalWith
      (fun _ V f ↦ LocallyOfFiniteType f ∧ QuasiCompact f ∧
        (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (y : Spec (CommRingCat.of Ω) ⟶ V),
          Finite ↥(pullback f y)) ∧ IsClosedImmersion (pullback.diagonal f)) F) :
    ∀ x : ModuliPoints F, IsClosed ({x} : Set (ModuliPoints F)) →
      IsClosed ({moduliPointMap (moduliRelativeDiagonal (moduliBaseStructure F)) x} :
        Set (ModuliPoints (moduliTwoFiberProduct (moduliBaseStructure F)
          (moduliBaseStructure F)))) := by
  sorry

end CategoryTheory
