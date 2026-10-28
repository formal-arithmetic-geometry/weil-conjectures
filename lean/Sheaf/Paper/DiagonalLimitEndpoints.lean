/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group X3
-/
module

public import Sheaf.Paper.DiagonalTowerLimitInterface

/-! # Normalized completed diagonal endpoints

Source: the diagonal tower limit proof, paragraphs (1) and (3).
(blueprint: lem-sfb-diagonal-limit-endpoints).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale

attribute [local irreducible] diagonalCompletedSource diagonalOrdinaryRlim
  diagonalSourceLimitMap diagonalTargetLimitMap diagonalRootLimitComparison
  diagonalSingleLimitComparison diagonalShiftedSingleLimitComparison
  diagonalCompletedRestriction

/-- The ordinary supported constant and root limits, their canonical derived-limit
comparisons, and intrinsic completeness of the two completed endpoints.

Source: blueprint `sk-prop-diagonal-tower-limit.proof.md`, paragraphs (1) and (3);
Stacks 099L and 099M (blueprint: lem-sfb-diagonal-limit-endpoints).
Proof: the cokernel presentation of D.ordinary identifies the source tower, including
its quotient maps, with the supported finite constant tower. Closed direct image is
exact and preserves limits; its limit is the restricted completed constant. The unit
section of this comparison is diagonalCompletedGenerator, so composing with each
finite projection gives the displayed source normalization. At level n the root
groups are ell^(n+1)-torsion, so their Z_l actions factor through
Z_l/ell^(n+1) = Z/ell^(n+1). Hence the underlying root comparison is Z_l-linear.
Forgetting scalars creates limits, giving t with underlying map precisely the
inverse of diagonalRootLimitComparison. Quotient transitions are
epic, as are root power transitions when ell is invertible. The Milnor calculation on
weakly contractible affines makes the canonical ordinary-to-derived-limit maps
isomorphisms. Uniqueness of total right derived limits identifies these maps with the
unit of L; compose with a and b and the shift comparison. DiagonalCompletionSpec makes
these same two limits intrinsically complete after forgetting constant scalars.
The flat coefficient comparisons from Z to constant Z_l and from constant Z_l to
the completed coefficient sheaf have the same finite quotients. The complete-object
equivalences of 099I first give orthogonality over constant Z_l and then transport
it to the completed category. No choice of a map between the endpoints occurs in this assertion. -/
theorem diagonal_limit_endpoints (ℓ : ℕ) [Fact ℓ.Prime]
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (hpℓ : p ≠ ℓ)
    (Y : Scheme.{u}) [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))] (hY : IsUnit (ℓ : Γ(Y, ⊤)))
    [HasDerivedCategory.{u + 1} (DiagonalAb (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (DiagonalMod ℓ (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (DiagonalSystems ℓ (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (ℕᵒᵖ ⥤ DiagonalAb (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (DiagonalCompleted ℓ (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (ℕᵒᵖ ⥤ DiagonalCompleted ℓ (diagonalSurface Y))]
    [HasExt.{u + 1} (DiagonalSystems ℓ (diagonalSurface Y))]
    (D : DiagonalDerivedReduction ℓ (diagonalScalarExtension ℓ (diagonalSurface Y)))
    (hcompletion : DiagonalCompletionSpec ℓ (diagonalSurface Y) D)
    (H : DiagonalSystems ℓ (diagonalSurface Y))
    (roots : H ⋙ diagonalForget ℓ (diagonalSurface Y) ≅
      Scheme.proEtaleRootsOfUnityTower (diagonalSurface Y) ℓ (Fact.out : ℓ.Prime))
    (a : D.T.obj ((DerivedCategory.singleFunctor _ 0).obj (diagonalIntegralSource Y)) ≅
      (DerivedCategory.singleFunctor _ 0).obj (D.ordinary.E.obj (diagonalIntegralSource Y)))
    (b : D.T.obj (((DerivedCategory.singleFunctor _ 0).obj
      (diagonalComparisonUnits Y))⟦(1 : ℤ)⟧) ≅
      ((DerivedCategory.singleFunctor _ 0).obj H)⟦(2 : ℤ)⟧) :
    ∃ (L : DiagonalRlim (DiagonalMod ℓ (diagonalSurface Y)))
      (s : (diagonalCompletedRestriction ℓ (diagonalSurface Y)).obj
        (diagonalCompletedSource ℓ Y) ≅ limit (D.ordinary.E.obj (diagonalIntegralSource Y)))
      (t : (diagonalCompletedRestriction ℓ (diagonalSurface Y)).obj
        (Scheme.purTwistZlModule (diagonalSurface Y) ℓ) ≅ limit H),
      (∀ n : ℕ,
        diagonalCompletedGenerator ℓ Y ≫ (diagonalForget ℓ (diagonalSurface Y)).map
          (s.hom ≫ limit.π (D.ordinary.E.obj (diagonalIntegralSource Y)) (op n)) =
        (diagonalScalarAdjunction ℓ (diagonalSurface Y)).unit.app (diagonalIntegralSource Y) ≫
          (diagonalForget ℓ (diagonalSurface Y)).map
            ((D.ordinary.π n).app (diagonalIntegralSource Y))) ∧
      HEq ((diagonalForget ℓ (diagonalSurface Y)).map t.hom)
        (diagonalRootLimitComparison ℓ (diagonalSurface Y) H roots).inv ∧
      IsIso (diagonalSourceLimitMap ℓ Y D a L s) ∧
      IsIso (diagonalTargetLimitMap ℓ Y D H b L t) ∧
      (∀ V : DerivedCategory (DiagonalCompleted ℓ (diagonalSurface Y)),
        IsIso (ℓ • 𝟙 V) → Subsingleton (V ⟶ diagonalCompletedDomain ℓ Y)) ∧
      (∀ V : DerivedCategory (DiagonalCompleted ℓ (diagonalSurface Y)),
        IsIso (ℓ • 𝟙 V) → Subsingleton (V ⟶ diagonalCompletedCodomain ℓ Y)) ∧
      (∀ V : DerivedCategory (DiagonalMod ℓ (diagonalSurface Y)),
        IsIso (ℓ • 𝟙 V) → Subsingleton (V ⟶
          (diagonalCompletedUnderlying ℓ (diagonalSurface Y)).obj
            (diagonalCompletedDomain ℓ Y))) ∧
      (∀ V : DerivedCategory (DiagonalMod ℓ (diagonalSurface Y)),
        IsIso (ℓ • 𝟙 V) → Subsingleton (V ⟶
          (diagonalCompletedUnderlying ℓ (diagonalSurface Y)).obj
            (diagonalCompletedCodomain ℓ Y))) := by sorry


end AlgebraicGeometry.ProEtale
