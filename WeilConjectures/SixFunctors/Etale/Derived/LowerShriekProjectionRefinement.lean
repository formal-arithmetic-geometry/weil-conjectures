/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.CompConjugate
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComparison.CompositionLaw
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjection

/-!
# The projection map and refinements of compactifications

For a refinement `r : c.Refinement d` of compactifications of `f : X ⟶ Y` whose square over `X`
is cartesian, the comparison `Rf_!(d) ⟶ Rf_!(c)`
(`AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactificationComparison`) intertwines the
projection maps `PF_d` and `PF_c`
(`AlgebraicGeometry.Etale.projectionMapOfCompactification_comparison`).
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] [Etale.UpperStarPreservesFlat A]
  [HasSmallSiteSheafify A]
  {FC : A → A → Type*} {CC : A → Type (u + 1)}
  [∀ (P Q : A), FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{u + 1} A FC]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
  [∀ Z : Scheme.{u}, Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]

namespace Etale

variable {X Y : Scheme.{u}} {f : X ⟶ Y} {c d : Compactification f} (r : c.Refinement d)

omit [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] [Etale.UpperStarPreservesFlat A] in
/-- The composition isomorphism `Rq_* ⋙ R(d.g)_* ≅ R(c.g)_*` of a refinement is the conjugate of
the composition isomorphism `D((c.g)^*) ≅ D((d.g)^*) ⋙ D(q^*)` under the derived adjunctions. -/
lemma rightDerivedFunctorCompIso'_refinementLowerStarComp_hom :
    (Functor.rightDerivedFunctorCompIso' (r.hom)_*[A] (d.g)_*[A]
        (refinementLowerStarComp A r)).hom =
      conjugateEquiv ((mapDerivedUpperStarLowerStarAdjunction A d.g).comp
          (mapDerivedUpperStarLowerStarAdjunction A r.hom))
        (mapDerivedUpperStarLowerStarAdjunction A c.g)
        (Functor.mapDerivedCategoryNatIso (Etale.upperStarComp A r.hom d.g c.g r.hom_g.symm) ≪≫
          Functor.mapDerivedCategoryCompIso _ _).hom :=
  Adjunction.rightDerivedFunctorCompIso'_hom_eq_conjugateEquiv
    (Etale.upperStarLowerStarAdjunction A r.hom) (Etale.upperStarLowerStarAdjunction A d.g)
    (Etale.upperStarLowerStarAdjunction A c.g) _ _ (by
      rw [refinementLowerStarComp_eq]
      exact (congrArg Iso.hom
        (Etale.conjugateIsoEquiv_upperStarComp A r.hom d.g c.g r.hom_g.symm)).symm)

/-- The comparison `Rf_!(d) ⟶ Rf_!(c)` along a refinement intertwines the projection maps. -/
lemma projectionMapOfCompactification_comparison (hcart : IsPullback c.i (𝟙 X) r.hom d.i)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology A))
    (L : DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    ((projectionMapOfCompactification A d).app K).app L ≫
        (rightDerivedLowerShriekOfCompactificationComparison A r hcart).app
          (((-⊗ᴸ-(X)[A]).obj K).obj (L((f)^*[A]).obj L)) =
      ((-⊗ᴸ-(Y)[A]).map ((rightDerivedLowerShriekOfCompactificationComparison A r hcart).app
          K)).app L ≫
        ((projectionMapOfCompactification A c).app K).app L := by
  sorry


end Etale

end AlgebraicGeometry
