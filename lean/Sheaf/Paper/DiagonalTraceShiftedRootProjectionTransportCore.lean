/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.DiagonalTraceRootTransport
public import Sheaf.Paper.DiagonalTraceProjectionEquations
/-! # Core shifted root-projection transport equation -/

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
The post-shift-isomorphism core of generic root-projection transport.  Removing
 the common source shift isomorphism makes this the finite projection transport
 equation itself; the enclosing theorem reinstates that common isomorphism.

Source: diagonal-limit clause (3), normalization of the root-limit comparison;
diagonal trace proof (1), root cone and exact single/shift comparisons.
(blueprint: lem-sfb-diagonal-trace-shifted-root-projection-transport-core).

Proof: expand the normalized shifted single comparison and the strict root
transport, apply the normalized ordinary-limit projection to the single complex,
then use the cone component equation.  Naturality of each shift comparison moves
those arrows through the finite projection; the canonical single comparisons
cancel in the displayed composite.
-/
theorem diagonalTrace_shiftedRootProjection_transport_core
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
    (shiftFunctor (DerivedCategory B) (2 : ℤ)).map
          ((F.mapDerivedCategorySingleFunctor 0).hom.app P ≫
            (DerivedCategory.singleFunctor B 0).map t.hom ≫ diagonalOrdinaryRlim L₀ H) ≫
        (Functor.commShiftIso L₀.R (2 : ℤ)).inv.app
          ((DerivedCategory.singleFunctor (ℕᵒᵖ ⥤ B) 0).obj H) ≫
        L₀.R.map b.inv ≫
        (L₀.projection n).app J ≫
        ((evaluation ℕᵒᵖ B).obj (op n)).mapDerivedCategory.map
          (b ≪≫
            (shiftFunctor (DerivedCategory (ℕᵒᵖ ⥤ B)) (2 : ℤ)).mapIso
              ((DerivedCategory.singleFunctor (ℕᵒᵖ ⥤ B) 0).mapIso e) ≪≫
            (shiftFunctor (DerivedCategory (ℕᵒᵖ ⥤ B)) (2 : ℤ)).mapIso
              ((V.mapDerivedCategorySingleFunctor 0).app N).symm ≪≫
            ((Functor.commShiftIso V.mapDerivedCategory (2 : ℤ)).app
              ((DerivedCategory.singleFunctor C 0).obj N)).symm).hom =
      (shiftFunctor (DerivedCategory B) (2 : ℤ)).map
          ((F.mapDerivedCategorySingleFunctor 0).hom.app P ≫
            (DerivedCategory.singleFunctor B 0).map (limit.lift (V.obj N) ⟨F.obj P, π⟩) ≫
            diagonalOrdinaryRlim L (V.obj N) ≫
            L.R.map ((V.mapDerivedCategorySingleFunctor 0).inv.app N)) ≫
        (Functor.commShiftIso (V.mapDerivedCategory ⋙ L.R) (2 : ℤ)).inv.app
          ((DerivedCategory.singleFunctor C 0).obj N) ≫
        (L.projection n).app
          (V.mapDerivedCategory.obj
            (((DerivedCategory.singleFunctor C 0).obj N)⟦(2 : ℤ)⟧)) := by
  sorry

end AlgebraicGeometry.ProEtale.DiagonalTrace
