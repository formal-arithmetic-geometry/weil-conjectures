/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A5
-/
module

public import Sheaf.Paper.DiagonalEvaluationUnit
public import Sheaf.Paper.KummerStrictAdjunctData

/-! # Identification and normalization of the surviving Kummer cohomology
Source: diagonal tower system proof, steps (3) and (4).
(blueprint: lem-sfb-strict-kummer-pure-kernel-normalization). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u w
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale

attribute [local instance 11000] kummerModuleHasExt kummerAbHasExt
attribute [local irreducible] CategoryTheory.Abelian.Ext DerivedCategory.singleFunctors
  DerivedCategory.singleFunctorIsoCompQ HasDerivedCategory.standard
  comparisonUpperStar cartierUnitsComparison cartierRootsComparison cartierRootsIso
  cartierProKummerUnit cartierProRootMap diagonalFiniteToPadic diagonalForget
  diagonalScalarExtension diagonalScalarAdjunction

/-- Roots identifications and the evaluated unit equation for a supplied pure
strict-system comparison. This definition constructs no data. -/
@[irreducible] def KummerPureKernelNormalization
    {A B : Type*} [Category A] [abA : Abelian A] [hA : HasExt.{w} A]
    [Category B] [abB : Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ B)]
    [HasExt.{w} (ℕᵒᵖ ⥤ B)]
    (ℓ : ℕ) (L : A ⥤ B) (U : B ⥤ A) (ad : L ⊣ U)
    [U.Additive] [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    (D : DiagonalDerivedReduction ℓ L)
    (C : ℕ → Type*) [catC : ∀ n, Category (C n)]
    (F : ∀ n, C n ⥤ B)
    (V : ∀ n, C n ⥤ A)
    (M : A) (rootsTower : ℕᵒᵖ ⥤ A) (P : ∀ n, C n)
    (κ : ∀ n, Ext M ((V n).obj (P n)) 1)
    (rootNorm : ∀ H : ℕᵒᵖ ⥤ B, (H ⋙ U ≅ rootsTower) →
      ∀ n, (H.obj (op n) ≅ (F n).obj (P n)) → Prop)
    (σ : ∀ n, V n ≅ F n ⋙ U) (η : ∀ n, DiagonalEvaluationUnit U ad D n)
    : Prop :=
    ∀ (H : ℕᵒᵖ ⥤ B)
    (b : D.T.obj (((DerivedCategory.singleFunctor A 0).obj M)⟦(1 : ℤ)⟧) ≅
      ((DerivedCategory.singleFunctor (ℕᵒᵖ ⥤ B) 0).obj H)⟦(2 : ℤ)⟧),
    ∃ (roots : H ⋙ U ≅ rootsTower)
      (t : ∀ n, H.obj (op n) ≅ (F n).obj (P n)),
      (∀ n, rootNorm H roots n (t n)) ∧
      ∀ n, (η n).unit.app (((DerivedCategory.singleFunctor A 0).obj M)⟦(1 : ℤ)⟧) ≫
        (diagonalEvaluationForget U n).mapDerivedCategory.map b.hom ≫
        ((diagonalEvaluationForget U n).mapDerivedCategory.commShiftIso (2 : ℤ)).hom.app
          ((DerivedCategory.singleFunctor (ℕᵒᵖ ⥤ B) 0).obj H) ≫
        (((diagonalEvaluationForget U n).mapDerivedCategorySingleFunctor 0).hom.app
          H)⟦(2 : ℤ)⟧' ≫
        ((DerivedCategory.singleFunctor A 0).map
          (U.map (t n).hom ≫ (σ n).inv.app (P n)))⟦(2 : ℤ)⟧' =
        -((κ n).hom⟦(1 : ℤ)⟧' ≫
          (shiftFunctorAdd (DerivedCategory A) (1 : ℤ) 1).inv.app
            ((DerivedCategory.singleFunctor A 0).obj ((V n).obj (P n))))

/-- Identify the surviving cohomology with roots, including its scalar action
and the unit equation, after a pure strict-system comparison has been supplied.
There is no assertion here that such a comparison exists.

Source: diagonal tower system proof, step (3), kernel and transitions, and
step (4), Kummer-unit calculation
(blueprint: lem-sfb-strict-kummer-pure-kernel-normalization).

Proof: on a common flat K-flat resolution, compare positive prime-power
reduction with the two-term coefficient resolution. Its kernel is the roots
sheaf by Kummer exactness and exact site comparison. The resolution transition
is multiplication by ell in degree minus one and identity in degree zero;
its kernel transition is the actual power-ell roots transition. Apply cohomology
to b and compose its inverse with this kernel identification. This defines
roots on H; naturality of cohomology gives the entire tower identification.
The coefficient action on the surviving kernel is the quotient action through
Z/ell^(n+1). Its canonical identification with the finite Tate line therefore
lifts uniquely to the p-adic-linear isomorphism t, and forgetting it is exactly
roots followed by cartierProRootMap. To fix the sign choose the negative kernel
identification, consistently for all levels. The complexes equation of eta on
the same resolution identifies its unshifted quotient unit with the positive
Kummer boundary, preceded by comparison on units. Shift once and insert the
inverse shift-addition comparison. The negative kernel identification gives
the negative of that shifted class, which is the displayed equation. A change
of the supplied b transports roots and t by its induced cohomology
isomorphism; no equation is asserted for independently chosen roots and t.
No derived isomorphism is constructed in this step, nor is equality of derived
arrows detected levelwise. The computation works at n=0, ell=2, and for the
zero sheaf without changing signs or dividing by two. -/
theorem strict_kummer_pure_kernel_normalization (ℓ : ℕ) [Fact ℓ.Prime] (W : Scheme.{u})
    (hW : IsUnit (ℓ : Γ(W, ⊤)))
    [HasDerivedCategory.{u + 1} (DiagonalAb W)]
    [HasDerivedCategory.{u + 1} (DiagonalSystems ℓ W)]
    [HasExt.{u + 1} (DiagonalSystems ℓ W)]
    (D : DiagonalDerivedReduction ℓ (diagonalScalarExtension ℓ W))
    (η : ∀ n, DiagonalEvaluationUnit (diagonalForget ℓ W)
      (diagonalScalarAdjunction ℓ W) D n) :
  KummerPureKernelNormalization
    (A := DiagonalAb W) (B := DiagonalMod ℓ W)
    (abA := diagonalAbSheafAbelian W) (abB := diagonalModuleSheafAbelian _ W)
    (hA := kummerAbHasExt W)
    ℓ (diagonalScalarExtension ℓ W) (diagonalForget ℓ W)
    (diagonalScalarAdjunction ℓ W) D
    (fun n => Sheaf (Scheme.ProEt.topology W)
      (ModuleCat.{u + 1} (diagonalResidue.{u} ℓ n)))
    (fun n => diagonalFiniteToPadic ℓ n W)
    (fun n => cartierForget (diagonalResidue.{u} ℓ n) W)
    ((comparisonUpperStar AddCommGrpCat.{u + 1} W).obj W.gmSheaf)
    (Scheme.proEtaleRootsOfUnityTower W ℓ (Fact.out : ℓ.Prime))
    (fun n => geoCartierLine (diagonalResidue.{u} ℓ n) (ℓ ^ (n + 1))
      (cartierResidue_cast ℓ (n + 1)) W)
    (fun n => kummerComparedUnit ℓ W hW n)
    (kummerRootNormalization ℓ W hW)
    (fun n ↦ diagonalFiniteForgetIso ℓ n W) η := by sorry

end AlgebraicGeometry.ProEtale
