/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.CounitFac

/-!
# The tensor comparison of the derived pullback on images of complexes

Let `Λ` be a commutative condensed ring and `f : X ⟶ Y` a morphism of schemes. On the images
`Q P`, `Q T` of complexes of module objects over `Λ_Y`, the tensor comparison
`m : Lf^* (Q P ⊗ᴸ Q T) ⟶ Lf^* (Q P) ⊗ᴸ Lf^* (Q T)` of the derived pullback
(`AlgebraicGeometry.ProEtale.CondensedRing.leftDerivedUpperStarTensor`) is the localization of
the comparison `f^* (P ⊗ T) ⟶ f^* P ⊗ f^* T` of complexes induced by the comonoidal structure of
`f^*`, through the identification `Lf^* ≅ D(f^*)` of the derived pullback of the exact functor
`f^*` with its levelwise extension and the lax monoidal structure of `Q`
(`AlgebraicGeometry.ProEtale.CondensedRing.leftDerivedUpperStarTensor_app_app_Q_obj`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- **The tensor comparison of `Lf^*` on images of complexes.** For complexes `P`, `T` of module
objects over `Λ_Y`, the comparison `Lf^* (Q P ⊗ᴸ Q T) ⟶ Lf^* (Q P) ⊗ᴸ Lf^* (Q T)`, followed by the
identifications `Lf^* (Q P) ≅ D(f^*) (Q P) ≅ Q (f^* P)` and the lax structure of `Q`, is the
image under `Lf^*` of the lax structure `Q P ⊗ᴸ Q T ⟶ Q (P ⊗ T)` followed by the same
identification and the localization of the comparison `f^* (P ⊗ T) ⟶ f^* P ⊗ f^* T` induced by
the comonoidal structure of `f^*`. -/
lemma leftDerivedUpperStarTensor_app_app_Q_obj
    (P T : CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) ℤ) :
    ((leftDerivedUpperStarTensor Λ f).app (DerivedCategory.Q.obj P)).app
        (DerivedCategory.Q.obj T) ≫
      ((f)^*⟦Λ⟧.leftDerivedFunctorIsoMapDerivedCategory.hom.app _ ≫
          (f)^*⟦Λ⟧.mapDerivedCategoryFactors.hom.app P) ▷ _ ≫
      _ ◁ ((f)^*⟦Λ⟧.leftDerivedFunctorIsoMapDerivedCategory.hom.app _ ≫
          (f)^*⟦Λ⟧.mapDerivedCategoryFactors.hom.app T) ≫
      Functor.LaxMonoidal.μ DerivedCategory.Q (((f)^*⟦Λ⟧.mapHomologicalComplex (.up ℤ)).obj P)
        (((f)^*⟦Λ⟧.mapHomologicalComplex (.up ℤ)).obj T) =
    (f)^*⟦Λ⟧.leftDerivedFunctor.map (Functor.LaxMonoidal.μ DerivedCategory.Q P T) ≫
      (f)^*⟦Λ⟧.leftDerivedFunctorIsoMapDerivedCategory.hom.app _ ≫
      (f)^*⟦Λ⟧.mapDerivedCategoryFactors.hom.app _ ≫
      DerivedCategory.Q.map (HomologicalComplex.mapBifunctorComparison
        (Functor.OplaxMonoidal.δNatTrans (f)^*⟦Λ⟧) (.up ℤ) P T) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
