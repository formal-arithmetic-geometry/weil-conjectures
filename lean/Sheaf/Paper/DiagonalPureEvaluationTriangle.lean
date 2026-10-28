/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A7
-/
module

public import Sheaf.Paper.DiagonalEvaluationUnit
public import Mathlib.CategoryTheory.Triangulated.Pretriangulated

/-! # Multiplication triangles after evaluating a pure strict reduction
Source: diagonal tower system proof, steps (2) and (3).
(blueprint: lem-sfb-diagonal-pure-evaluation-triangle). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u w
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale

attribute [local irreducible] DerivedCategory.singleFunctors
  DerivedCategory.singleFunctorIsoCompQ HasDerivedCategory.standard
  diagonalScalarExtension diagonalScalarAdjunction diagonalForget

/-- The canonical evaluation comparison for a supplied pure strict-system isomorphism.
Its three factors are evaluation, the exact functor's shift comparison, and its single
comparison. No cohomology identification is chosen.
Source: exact evaluation comparisons in diagonal tower system proof, step (3)
(blueprint: lem-sfb-diagonal-pure-evaluation-triangle). -/
@[irreducible] def diagonalPureEvaluationIso
    {A B : Type*} [Category A] [Abelian A] [Category B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ B)]
    (U : B ⥤ A) [U.Additive] [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    {Z : DerivedCategory (ℕᵒᵖ ⥤ B)} (H : ℕᵒᵖ ⥤ B)
    (b : Z ≅ ((DerivedCategory.singleFunctor (ℕᵒᵖ ⥤ B) 0).obj H)⟦(2 : ℤ)⟧)
    (n : ℕ) :
    (diagonalEvaluationForget U n).mapDerivedCategory.obj Z ≅
      ((DerivedCategory.singleFunctor A 0).obj (U.obj (H.obj (op n))))⟦(2 : ℤ)⟧ :=
  (diagonalEvaluationForget U n).mapDerivedCategory.mapIso b ≪≫
    ((diagonalEvaluationForget U n).mapDerivedCategory.commShiftIso (2 : ℤ)).app
      ((DerivedCategory.singleFunctor (ℕᵒᵖ ⥤ B) 0).obj H) ≪≫
    (shiftFunctor (DerivedCategory A) (2 : ℤ)).mapIso
      (((diagonalEvaluationForget U n).mapDerivedCategorySingleFunctor 0).app H)



/-- The multiplication-triangle and transition property, kept folded when
specializing to concrete sheaf categories. This is a proposition containing no
chosen data.
Source: diagonal tower proof, steps (2) and (3)
(blueprint: lem-sfb-diagonal-pure-evaluation-triangle). -/
@[irreducible] def PureEvaluationTriangle
    {A B : Type*} [Category A] [Abelian A] [Category B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ B)]
    (ℓ : ℕ) (L : A ⥤ B) (U : B ⥤ A) (ad : L ⊣ U)
    [U.Additive] [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    (D : DiagonalDerivedReduction ℓ L) (η : ∀ n, DiagonalEvaluationUnit U ad D n)
    (M : A) (H : ℕᵒᵖ ⥤ B)
    (b : D.T.obj (((DerivedCategory.singleFunctor A 0).obj M)⟦(1 : ℤ)⟧) ≅
      ((DerivedCategory.singleFunctor (ℕᵒᵖ ⥤ B) 0).obj H)⟦(2 : ℤ)⟧) : Prop :=
  ∃ d : ∀ n, U.obj (H.obj (op n)) ⟶ M,
    (∀ n, Pretriangulated.Triangle.mk
      (ℓ ^ (n + 1) • 𝟙 (((DerivedCategory.singleFunctor A 0).obj M)⟦(1 : ℤ)⟧))
      ((η n).unit.app (((DerivedCategory.singleFunctor A 0).obj M)⟦(1 : ℤ)⟧) ≫
        (diagonalPureEvaluationIso U H b n).hom)
      (((DerivedCategory.singleFunctor A 0).map (d n))⟦(2 : ℤ)⟧' ≫
        (shiftFunctorAdd (DerivedCategory A) (1 : ℤ) 1).hom.app
          ((DerivedCategory.singleFunctor A 0).obj M)) ∈ distTriang (DerivedCategory A)) ∧
    ∀ n, U.map (H.map (homOfLE (Nat.le_succ n)).op) ≫ d n =
      d (n + 1) ≫ (ℓ • 𝟙 M)

/-- Evaluated reduction is the cofiber of prime-power multiplication, and its
cofiber boundaries have transition multiplier ell. This statement involves an arbitrary
integral sheaf M; it uses no roots, Tate line, or Kummer boundary.

Source: diagonal tower system proof, steps (2) and (3), the map of two-term resolutions
with components (ell,1)
(blueprint: lem-sfb-diagonal-pure-evaluation-triangle).

Proof: choose a flat-term K-flat resolution P of M[1]. Nonzero integer multiplication
is monic on every flat term and remains so after the exact p-adic extension.
The quotient universal property of D.ordinary, together with the canonical equality
Z_ell/ell^(n+1)=Z/ell^(n+1), identifies its underlying evaluated quotient with the
integral cokernel of ell^(n+1), carrying the scalar-adjunction unit to the quotient map.
The resulting degreewise short exact sequence gives the multiplication
triangle. Uniqueness of pointwise left derived functors makes D's counit invertible
on P, and the complexes equation of eta identifies the middle arrow with its quotient
unit. Transport through the resolution and the supplied b. The last arrow is a map
between single sheaves shifted twice, hence uniquely the shifted image of d_n by full
faithfulness. For successive levels the map of short exact sequences is (ell,1,quotient).
Naturality of the short-exact-sequence triangle gives d_(n+1) followed by ell equals
the underlying transition followed by d_n. The same resolution at every level is
essential; neither a family of unrelated triangles nor levelwise detection of derived
morphisms is used. This applies to M=0 and to n=0 without alteration. -/
theorem diagonal_pure_evaluation_triangle (ℓ : ℕ) [Fact ℓ.Prime] (W : Scheme.{u})
    [HasDerivedCategory.{u + 1} (DiagonalAb W)]
    [HasDerivedCategory.{u + 1} (DiagonalSystems ℓ W)]
    (D : DiagonalDerivedReduction ℓ (diagonalScalarExtension ℓ W))
    (η : ∀ n, DiagonalEvaluationUnit (diagonalForget ℓ W)
      (diagonalScalarAdjunction ℓ W) D n)
    (M : DiagonalAb W) (H : DiagonalSystems ℓ W)
    (b : D.T.obj (((DerivedCategory.singleFunctor (DiagonalAb W) 0).obj M)⟦(1 : ℤ)⟧) ≅
      ((DerivedCategory.singleFunctor (DiagonalSystems ℓ W) 0).obj H)⟦(2 : ℤ)⟧) :
    PureEvaluationTriangle ℓ (diagonalScalarExtension ℓ W) (diagonalForget ℓ W)
      (diagonalScalarAdjunction ℓ W) D η M H b := by sorry

end AlgebraicGeometry.ProEtale
