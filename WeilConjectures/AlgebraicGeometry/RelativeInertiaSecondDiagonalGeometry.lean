/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RelativeModuliInertia
public import WeilConjectures.AlgebraicGeometry.DmStackMorphismProperties

/-! # Relative inertia and the second diagonal

Source: Stacks Project, Tags 04XS, 050Q and 034H; higher diagonals preceding Tag 0CL0
(blueprint: lem-sfb-relative-inertia-second-diagonal-geometry).
-/

@[expose] public section

set_option autoImplicit false

universe u v₁ w₁ v₂ w₂

namespace CategoryTheory

/-- The relative diagonal and inertia projection are representable by algebraic spaces;
inertia is algebraic and identifies over the source with the self-product of the diagonal.
Under this identification the second diagonal is the neutral section.

Source: Stacks Project, Tags 04XS, 050Q, 034H, and higher diagonals preceding Tag 0CL0
(blueprint: lem-sfb-relative-inertia-second-diagonal-geometry).

Proof: Form B = F ×_G F and D = F ×_B F using the relative diagonal on both sides.
Algebraic stacks are closed under these fibre products, and 04XS makes the diagonal
representable. An object of D is (x,y,(i,k)) with h(i)=h(k). Send it to (x,k⁻¹i),
and an arrow (a,b) to a. The inverse sends (x,α) to (x,x,(α,1)) and a to (a,a).
The first composite is the identity. The other has natural comparison (1,k);
naturality is precisely bk=ma for an arrow whose target comparison is (l,m).
Both formulas commute with base pullback and retain the first projection. The
second diagonal has i=k=1 and therefore becomes the identity-automorphism section.
The first projection D → F is a base change of the relative diagonal, hence is
representable. Transfer its scheme tests along the equivalence to get the actual
inertia projection's representability. Finally transport descent data, diagonal
scheme tests and a smooth surjective atlas of D along the equivalence. This proves
algebraicity of relative inertia, with no extra assumption on h. -/
theorem relative_inertia_second_diagonal_geometry {S : AlgebraicGeometry.Scheme.{u}}
    (F : BasedCategory.{v₁, w₁} (Over S)) (G : BasedCategory.{v₂, w₂} (Over S))
    (h : BasedFunctor F G) (hF : IsAlgebraicModuliStack F) (hG : IsAlgebraicModuliStack G) :
    IsRepresentableByAlgebraicSpaces (moduliRelativeDiagonal h) ∧
    IsAlgebraicModuliStack (relativeModuliInertia h) ∧
    IsRepresentableByAlgebraicSpaces (relativeModuliInertiaProjection h) ∧
    ∃ e : BasedFunctor
        (moduliTwoFiberProduct (moduliRelativeDiagonal h) (moduliRelativeDiagonal h))
        (relativeModuliInertia h),
      e.toFunctor.IsEquivalence ∧
      Nonempty (ModuliTwoIso (e.comp (relativeModuliInertiaProjection h))
        (moduliTwoFiberFst (moduliRelativeDiagonal h) (moduliRelativeDiagonal h))) ∧
      Nonempty (ModuliTwoIso ((moduliRelativeDiagonal (moduliRelativeDiagonal h)).comp e)
        (relativeModuliInertiaNeutral h)) := by
  sorry

/-- Over the base scheme, relative inertia is the already defined absolute inertia.
The canonical inclusion retains objects, automorphisms, arrows and the projection.

Source: Stacks Project, Tag 050Q, absolute case, and Categories Tag 034H
(blueprint: lem-sfb-relative-inertia-second-diagonal-geometry).

Proof: The structural functor is the projection to Sch/S. For every absolute inertia
object its automorphism is vertical, so its image is the identity by definition.
Thus every absolute inertia object belongs to the defining full subcategory of
relative inertia. The inclusion is fully faithful and essentially surjective,
without any change to objects, automorphisms, arrows, or their base projections. -/
theorem relative_moduli_inertia_absolute {S : AlgebraicGeometry.Scheme.{u}}
    (F : BasedCategory.{v₁, w₁} (Over S)) (hF : IsAlgebraicModuliStack F) :
    (relativeModuliInertiaToAbsolute (moduliBaseStructure F)).toFunctor.IsEquivalence := by
  sorry

end CategoryTheory
