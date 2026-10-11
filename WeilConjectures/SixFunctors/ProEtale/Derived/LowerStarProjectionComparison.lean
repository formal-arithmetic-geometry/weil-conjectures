/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapMate
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Monoidal
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula
public import WeilConjectures.SixFunctors.ProEtale.Comparison.Flat
public import WeilConjectures.SixFunctors.ProEtale.Comparison.Monoidal
public import WeilConjectures.SixFunctors.ProEtale.Derived.Comparison
public import WeilConjectures.SixFunctors.ProEtale.Derived.LowerShriekComparison
public import WeilConjectures.SixFunctors.ProEtale.Derived.LowerStarProjection

/-!
# The comparison carries the étale projection map of `Rg_*` to the pro-étale one
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

variable {Z Y : Scheme.{u}} (g : Z ⟶ Y)

lemma Etale.leftDerivedUpperStarTensorComparison_eq [Etale.UpperStarPreservesFlat A] :
    Etale.leftDerivedUpperStarTensorComparison A g =
      (Etale.upperStar A g).leftDerivedTensorComparison :=
  rfl

lemma ProEtale.leftDerivedUpperStarTensorComparison_eq [ProEtale.UpperStarPreservesFlat A] :
    ProEtale.leftDerivedUpperStarTensorComparison A g =
      (ProEtale.upperStar A g).leftDerivedTensorComparison :=
  rfl

namespace ProEtale

variable [Etale.UpperStarPreservesFlat A] [ProEtale.UpperStarPreservesFlat A]
  [∀ X : Scheme.{u}, (ν^*(X)[A]).PreservesFlat]

/-- The isomorphism `Lg^* ∘ Lν_Y^* ≅ Lν_Z^* ∘ Lg^*` of derived functors `D(Y_ét) ⥤ D(Z_proét)`,
obtained by deriving the isomorphism `g^* ν_Y^* ≅ ν_Z^* g^*` of
`AlgebraicGeometry.ProEtale.comparisonUpperStarCompUpperStarIso`. -/
noncomputable abbrev leftDerivedComparisonUpperStarCompUpperStarIso :
    L(ν^*(Y)[A]) ⋙ L(ProEtale.upperStar A g) ≅ L(Etale.upperStar A g) ⋙ L(ν^*(Z)[A]) :=
  Functor.leftDerivedFunctorCompNatIso (Etale.upperStar A g) ν^*(Z)[A] ν^*(Y)[A]
    (ProEtale.upperStar A g) (comparisonUpperStarCompUpperStarIso A g)

/-- The tensor comparisons of `Lg^*` on the étale and pro-étale sites and those of `Lν^*` are
compatible with `AlgebraicGeometry.ProEtale.leftDerivedComparisonUpperStarCompUpperStarIso`:
the comparison `Lν_Z^* Lg^*(K ⊗ᴸ M) ⟶ Lν_Z^* Lg^* K ⊗ᴸ Lν_Z^* Lg^* M` obtained from the étale
pullback agrees with the one obtained from the pro-étale pullback. -/
lemma comparisonCompatible_leftDerivedComparisonUpperStarCompUpperStarIso :
    Adjunction.ComparisonCompatible (leftDerivedComparisonUpperStarCompUpperStarIso A g)
      (Etale.leftDerivedUpperStarTensorComparison _ g)
      (ProEtale.leftDerivedUpperStarTensorComparison _ g)
      (asIso (ν^*(Z)[A]).leftDerivedTensorComparison)
      (asIso (ν^*(Y)[A]).leftDerivedTensorComparison) := by
  intro a b
  rw [Etale.leftDerivedUpperStarTensorComparison_eq,
    ProEtale.leftDerivedUpperStarTensorComparison_eq, asIso_hom, asIso_hom,
    Functor.map_leftDerivedTensorComparison_comp_eq_of_iso _ _ _ _
      (comparisonUpperStarCompUpperStarIso A g), tensorHom_def]
  rfl

end ProEtale

end AlgebraicGeometry
