/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalTowerSystem
public import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalTowerLimitInterface
public import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalLimitAssembly
public import WeilConjectures.AlgebraicGeometry.Completed.CompletedCondensedCoefficients
public import WeilConjectures.AlgebraicGeometry.Internal.InternalSignedTateTwist
public import WeilConjectures.AlgebraicGeometry.AdicCompletion.DerivedCompletionSupplement
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.CategoryTheory.Triangulated.Functor
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSurjectiveTowerDerivedLimitSupplement
import WeilConjectures.ProperBaseChange.RingedStrictTowerHomotopyLimitIndependentCoefficients
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.ClosedImmersion
import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import WeilConjectures.CategoryTheory.Ringed.RingedTowerPushforwardLimitComparison
import WeilConjectures.Algebra.Homology.LineUnbounded.LineUnboundedDerivedTensor
import WeilConjectures.ProperBaseChange.ConstantCompletionCore
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvr
import WeilConjectures.AlgebraicGeometry.Completed.CompletedCoefficientFiniteUnit
import WeilConjectures.CategoryTheory.AdicSites.CompletionUnitFiniteProjection
import WeilConjectures.Algebra.Homology.SixFunctors.OrdinaryDerivedChangeOfRings

/-! # The completed diagonal class on an arbitrary base

Source: latest blueprint, sec-six-functors-basics/sk-prop-diagonal-tower/
sk-prop-diagonal-tower-limit.md, clauses 1--3; Stacks Tags 099L and 099I
(blueprint: det-prop-diagonal-tower-limit).

The strict towers have constant discrete Z_l coefficients. Their completed endpoints
use the limit ring sheaf, canonically identified with the pulled-back condensed ring.
The existing sectionwise module presentation retains the coefficient action and is
canonically equivalent to internal modules. Positive level n+1 is indexed by n.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale

/-- The supported coefficient tower and the root tower have the completed endpoints,
and the limit of the strict diagonal class has a unique completed-coefficient lift.
Its finite reductions are the normalized torsion Cartier classes.

Source: latest blueprint, clauses 1 and 3; Stacks Tags 099L and 099I
(blueprint: det-prop-diagonal-tower-limit).

Proof:
1. On the compatible-root cover the root tower is the quotient tower. Its power
   transitions and the quotient transitions are epimorphisms. Repleteness and exact
   products identify their derived limits with their ordinary limits. The normalized
   coefficient limit comparison gives Z_l and the coordinatewise root limit gives Z_l(1).
2. The diagonal complement is quasi-compact, as checked on the four affine product
   charts by D(x-y) and D(xy-1). Thus diagonal direct image is exact and preserves
   limits. The same surjective-tower comparison gives the supported completed source.
3. The strict-system theorem identifies c with simultaneous derived reduction of the
   positive Cartier boundary. Its completion specification identifies Rlim(c) with
   completion of that boundary, including the completion unit. Both endpoints are
   derived ell-complete, equivalently right orthogonal to ell-invertible complexes.
4. For the constant Z_l ring, completion along (ell) is the completed coefficient
   sheaf just identified. Constant/completed scalar restriction is an equivalence on
   complete objects. Full faithfulness gives exactly one lift of the entire underlying
   limit arrow, with the source generator and root-limit comparisons fixed.
5. Reduction of the completion unit is invertible. Its inverse is adjoint to the
   finite tower projection. Naturality and the finite change-of-rings comparison
   identify each reduction of the lifted arrow with c_n, the positive torsion Cartier
   cycle class. This uses the unit/projection comparison, not uniqueness from levels. -/
theorem diagonalTower_limit_general (ℓ : ℕ) [Fact ℓ.Prime] (Y : Scheme.{u})
    (hY : IsUnit (ℓ : Γ(Y, ⊤)))
    [HasDerivedCategory.{u + 1} (DiagonalAb (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (DiagonalMod ℓ (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (DiagonalSystems ℓ (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (ℕᵒᵖ ⥤ DiagonalAb (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (DiagonalCompleted ℓ (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (ℕᵒᵖ ⥤ DiagonalCompleted ℓ (diagonalSurface Y))]
    [HasExt.{u + 1} (DiagonalSystems ℓ (diagonalSurface Y))]
    (D : DiagonalDerivedReduction ℓ (diagonalScalarExtension ℓ (diagonalSurface Y)))
    (hcompletion : DiagonalCompletionSpec ℓ (diagonalSurface Y) D)
    (hsystem : DiagonalCycleSystemSpec ℓ Y hY D) :
    DiagonalCompletedLimitSpec ℓ Y hY D := by
  sorry

/-- Derived direct image on strict constant-coefficient towers commutes with Rlim
and is computed levelwise. Both comparisons are normalized by their full derived
units and by the canonical projections.

Source: latest blueprint, clause 1; Stacks Tag 099L
(blueprint: det-prop-diagonal-tower-limit).

Proof: inverse image is exact and left adjoint to direct image, both on sheaves
and on strict systems. The constant-system functor is exact and left adjoint to
limit. Evaluation also has an exact left adjoint. These right adjoints preserve
K-injective complexes, so their total right derived functors have the stated
composite and evaluation comparisons. Ordinary direct image commutes with limits;
its comparison is limit.post. Uniqueness in the right-derived universal properties
fixes the two comparison maps by their cochain units. Naturality of the limit
projections gives the final compatibility equation on all derived systems. -/
theorem diagonalTower_directImage_general (ℓ : ℕ) [Fact ℓ.Prime]
    {X Y : Scheme.{u}} (hX : IsUnit (ℓ : Γ(X, ⊤))) (hY : IsUnit (ℓ : Γ(Y, ⊤)))
    (f : X ⟶ Y)
    [HasDerivedCategory.{u + 1} (DiagonalMod ℓ X)]
    [HasDerivedCategory.{u + 1} (DiagonalMod ℓ Y)]
    [HasDerivedCategory.{u + 1} (DiagonalSystems ℓ X)]
    [HasDerivedCategory.{u + 1} (DiagonalSystems ℓ Y)] :
    ∃ (LX : DiagonalRlim (DiagonalMod ℓ X)) (LY : DiagonalRlim (DiagonalMod ℓ Y))
      (Rf : DiagonalRightDerived ((lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[ℓ])) f)))
      (Rt : DiagonalRightDerived ((Functor.whiskeringRight ℕᵒᵖ
        (DiagonalMod ℓ X) (DiagonalMod ℓ Y)).obj
          ((lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[ℓ])) f))))
      (e : ∀ n : ℕ, Rt.R ⋙
        ((evaluation ℕᵒᵖ (DiagonalMod ℓ Y)).obj (op n)).mapDerivedCategory ≅
        ((evaluation ℕᵒᵖ (DiagonalMod ℓ X)).obj (op n)).mapDerivedCategory ⋙ Rf.R)
      (c : LX.R ⋙ Rf.R ≅ Rt.R ⋙ LY.R)
      (c₀ : (lim : (ℕᵒᵖ ⥤ (DiagonalMod ℓ X)) ⥤ (DiagonalMod ℓ X)) ⋙
          (lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[ℓ])) f) ≅
        (Functor.whiskeringRight ℕᵒᵖ (DiagonalMod ℓ X) (DiagonalMod ℓ Y)).obj
          ((lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[ℓ])) f)) ⋙ lim),
      (∀ H : (ℕᵒᵖ ⥤ (DiagonalMod ℓ X)),
        c₀.hom.app H = limit.post H
          ((lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[ℓ])) f))) ∧
      (∀ P : CochainComplex ((ℕᵒᵖ ⥤ (DiagonalMod ℓ X))) ℤ,
        Rf.η.app (((lim : (ℕᵒᵖ ⥤ (DiagonalMod ℓ X)) ⥤ (DiagonalMod ℓ X)).mapHomologicalComplex
          (.up ℤ)).obj P) ≫ Rf.R.map (LX.η.app P) ≫ c.hom.app (DerivedCategory.Q.obj P) =
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex c₀.hom (.up ℤ)).app P) ≫
          LY.η.app ((((Functor.whiskeringRight ℕᵒᵖ
            (DiagonalMod ℓ X) (DiagonalMod ℓ Y)).obj
              ((lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[ℓ])) f))).mapHomologicalComplex
                (.up ℤ)).obj P) ≫ LY.R.map (Rt.η.app P)) ∧
      (∀ (P : CochainComplex ((ℕᵒᵖ ⥤ (DiagonalMod ℓ X))) ℤ), P.IsKInjective → ∀ n : ℕ,
        ((evaluation ℕᵒᵖ (DiagonalMod ℓ Y)).obj (op n)).mapDerivedCategory.map (Rt.η.app P) ≫
          (e n).hom.app (DerivedCategory.Q.obj P) ≫
          Rf.R.map (((evaluation ℕᵒᵖ (DiagonalMod ℓ X)).obj
            (op n)).mapDerivedCategoryFactors.hom.app P) =
        ((evaluation ℕᵒᵖ (DiagonalMod ℓ Y)).obj (op n)).mapDerivedCategoryFactors.hom.app
          ((((Functor.whiskeringRight ℕᵒᵖ (DiagonalMod ℓ X) (DiagonalMod ℓ Y)).obj
            ((lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[ℓ])) f))).mapHomologicalComplex
              (.up ℤ)).obj P) ≫ Rf.η.app (P.asFunctor.obj (op n))) ∧
      ∀ (M : DerivedCategory ((ℕᵒᵖ ⥤ (DiagonalMod ℓ X)))) (n : ℕ),
        c.hom.app M ≫ (LY.projection n).app (Rt.R.obj M) ≫ (e n).hom.app M =
          Rf.R.map ((LX.projection n).app M) := by
  sorry

end AlgebraicGeometry.ProEtale
