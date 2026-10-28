/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.DiagonalTraceRootTransport
public import Sheaf.Paper.DiagonalTraceProjectionEquations

/-! # Generic shifted root-projection transport -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe a b c va vb vc wa wb wc
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.DiagonalTrace

attribute [local instance] AlgebraicGeometry.ProEtale.diagonalHasLimit
  AlgebraicGeometry.ProEtale.diagonalConstantTowerLimits

attribute [local irreducible] DerivedCategory Functor.mapDerivedCategory

/--
The generic categorical transport calculation behind a normalized root projection.
It uses only an exact functor, an exact system-valued functor, a cone isomorphism,
and the component equations of that cone.  The coefficient objects and their
line maps are absent; those are supplied by the specialization in
`diagonalTrace_rootProjection`.

Source: diagonal-limit clause (3), normalization of the root-limit comparison;
diagonal trace proof (1), root cone and exact single/shift comparisons.
(blueprint: lem-sfb-diagonal-trace-root-projection).

Proof: apply the normalized ordinary-limit projection to the single complex,
transport it along the system isomorphism, and use the cone component equation.
Naturality of the shift comparison moves the transported arrow through the
finite projection.  The remaining single and shift comparisons cancel in
`rootSystemTransport`, while the common derived-unit normalization identifies
the two right-derived-limit models.
-/
theorem diagonalTrace_shiftedRootProjection_transport
    {A : Type*} {B : Type*} {C : Type*}
    [Category A] [Category B] [Category C] [Abelian A] [Abelian B] [Abelian C]
    [HasLimitsOfShape ℕᵒᵖ B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory (ℕᵒᵖ ⥤ B)] [HasDerivedCategory C]
    (F : A ⥤ B) (V : C ⥤ (ℕᵒᵖ ⥤ B)) [F.Additive] [V.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    (L₀ L : DiagonalRlim B) (P : A) (N : C)
    (H : ℕᵒᵖ ⥤ B) (J : DerivedCategory (ℕᵒᵖ ⥤ B))
    (b : J ≅ ((DerivedCategory.singleFunctor _ 0).obj H)⟦(2 : ℤ)⟧)
    (t : F.obj P ≅ limit H) (e : H ≅ V.obj N)
    (π : (Functor.const ℕᵒᵖ).obj (F.obj P) ⟶ V.obj N)
    (hcone : ∀ n : ℕ, t.hom ≫ limit.π H (op n) ≫ e.hom.app (op n) = π.app (op n))
    (n : ℕ) :
    rootProjectionEquation L₀.R
      ((evaluation ℕᵒᵖ B).obj (op n)).mapDerivedCategory
      (L₀.projection n)
      (diagonalShiftedSingleLimitComparison F L₀ P H J t b)
      (rootSystemTransport V N b e).hom
      (shiftedComparison F.mapDerivedCategory (V.mapDerivedCategory ⋙ L.R)
        (exactConeComparison F V L P N π) 2 ≫ (L.projection n).app _) := by
  sorry

end AlgebraicGeometry.ProEtale.DiagonalTrace
