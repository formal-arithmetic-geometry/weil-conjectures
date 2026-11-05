/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.HomologyAmplitude
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.SixFunctors.Etale.Derived.GlobalSections
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.ProEtale.Comparison.Defs
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriek
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.GlobalSections

/-!
# Pro-étale cohomological dimension through the comparison morphism

Blueprints `rem-sf-fullcd-reduction` (3) and `rem-sf-fullcd-general-form` (a): the global
sections on the pro-étale site factor through the comparison morphism,
`Γ(X_proét, -) = Γ(X_ét, -) ∘ ν_*`, so `RΓ(X_proét, -) ≅ RΓ(X_ét, -) ∘ Rν_*`
(`AlgebraicGeometry.ProEtale.comparisonLowerStarCompRightDerivedGlobalSectionsIso`). If the étale
cohomology of `X` vanishes above `e` for every sheaf (the étale factor, `e = 2 dim X` for a
finite-type scheme over an algebraically closed field) and `R^q ν_* F = 0` for `q > M` and every
pro-étale sheaf `F`, then `H^r(X_proét, F) = 0` for `r > M + e`
(`AlgebraicGeometry.ProEtale.isZero_homology_rightDerivedGlobalSections_of_comparison`): unbounded
degrees can only enter through the comparison direct images `R^q ν_*`. That is exactly where the
counterexample of `rem-sf-fullcd-counterexample` puts them.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  (X : Scheme.{u})

/-- The global sections on the pro-étale site factor through the comparison morphism:
`Γ(X_ét, ν_* F) = (ν_* F)(X) = F(X) = Γ(X_proét, F)`, both sites having `X` itself as terminal
object. -/
noncomputable def comparisonLowerStarCompGlobalSectionsIso :
    ν_*(X)[A] ⋙ Sheaf.Γ X.smallEtaleTopology A ≅ Sheaf.Γ (Scheme.ProEt.topology X) A :=
  Functor.isoWhiskerLeft _ (Sheaf.ΓNatIsoSheafSections _ _
      (MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale X)) ≪≫
    Iso.refl _ ≪≫ (Sheaf.ΓNatIsoSheafSections _ _ (Scheme.ProEt.isTerminalMkId X)).symm

/-- The Leray isomorphism `RΓ(X_ét, Rν_* K) ≅ RΓ(X_proét, K)` for the comparison morphism:
the composition of right derived functors applied to
`AlgebraicGeometry.ProEtale.comparisonLowerStarCompGlobalSectionsIso`, valid since `ν_*` is right
adjoint to the exact functor `ν^*` and hence preserves K-injective complexes. -/
noncomputable def comparisonLowerStarCompRightDerivedGlobalSectionsIso :
    R(ν_*(X)[A]) ⋙ Etale.rightDerivedGlobalSections A X ≅ rightDerivedGlobalSections A X :=
  have : (ν_*(X)[A]).PreservesKInjectiveComplexes :=
    (comparisonAdjunction A X).preservesKInjectiveComplexes
  Functor.rightDerivedFunctorCompIso' _ _ (comparisonLowerStarCompGlobalSectionsIso A X)

end AlgebraicGeometry.ProEtale
