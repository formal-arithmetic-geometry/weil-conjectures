/- Copyright (c) 2026 The SHEAF contributors. -/
module

public import Sheaf.AlgebraicGeometry.OpenDerivedAdditiveStalkIso

/-! # Representative coherence for exact open stalk restriction

Source: Stacks Project, Tags 0098, 08DW and 015F; exact localization factorization.
(blueprint: lem-pc-open-stalk-representative-coherence).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry
open SingleComplexBaseChange

/-- Exact open stalk comparison on a morphism of representatives.

Proof: first apply comparisonStalkHomologyIso_naturality to a. Expand the
comparison for the restricted representative and openDerivedAdditiveStalkIso.
Apply mapDerivedCategoryCompIso_fac to the composites of restriction, stalk
and forgetting scalars, and mapDerivedCategoryNatIso_fac to the same-germ
comparison gamma. Apply mapDerivedCategoryHomologyFunctorIso_hom_app_Q to
both forgetful functors. The localization factors cancel with their inverses,
leaving homology of the stalk map of a followed by gamma. The naturality of
ShortComplex.mapHomologyIso gives the displayed inverse factor at the source
and direct factor at the target. All equalities are natural-transformation
identities, so zero complexes and zero homology require no extra hypotheses;
for the top open this specializes to the identity restriction comparison.
An empty open has no point z.
Source: Stacks Project, Tags 0098, 08DW and 015F; the exact functor factorization
identities named above.
(blueprint: lem-pc-open-stalk-representative-coherence). -/
theorem openStalk_representative_coherence
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (X : Scheme.{u}) (U : X.Opens) (z : U.toScheme) (i : ℤ)
    (M : CochainComplex (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) ℤ)
    (N : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ) :
    letI : (schemeOpenRestriction X U).Additive := schemeOpenRestriction_additive X U
    let R := schemeOpenRestriction X U
    let L₀ := RingedSpace.moduleStalkFunctor U.toScheme.toRingedSpace z
    let L := RingedSpace.moduleStalkFunctor X.toRingedSpace z.val
    let F₀ := forget₂ (ModuleCat.{u} (U.toScheme.presheaf.stalk z)) AddCommGrpCat.{u}
    let F := forget₂ (ModuleCat.{u} (X.presheaf.stalk z.val)) AddCommGrpCat.{u}
    let S₀ := (L₀.mapHomologicalComplex (.up ℤ)).obj M
    let S := (L.mapHomologicalComplex (.up ℤ)).obj N
    let γ : R ⋙ L₀ ⋙ F₀ ≅ L ⋙ F :=
      Functor.isoWhiskerRight (Scheme.Modules.overFunctorEquiv U) (L₀ ⋙ F₀) ≪≫
      Scheme.Modules.restrictStalkNatIso U.ι z
    ∀ (a : M ⟶ (R.mapHomologicalComplex (.up ℤ)).obj N),
      let b := DerivedCategory.Q.map a ≫ R.mapDerivedCategoryFactors.inv.app N
      let ρ := (F₀.mapHomologicalComplex (.up ℤ)).map
          ((L₀.mapHomologicalComplex (.up ℤ)).map a) ≫
        (NatTrans.mapHomologicalComplex γ.hom (.up ℤ)).app N
      F₀.map (comparisonStalkHomologyIso U.toScheme z M i).inv ≫
          F₀.map ((comparisonStalkCohomology U.toScheme z i).map b) ≫
          (openDerivedAdditiveStalkIso X U z i).hom.app (DerivedCategory.Q.obj N) =
        ((S₀.sc i).mapHomologyIso F₀).inv ≫ HomologicalComplex.homologyMap ρ i ≫
          ((S.sc i).mapHomologyIso F).hom ≫
          F.map (comparisonStalkHomologyIso X z.val N i).inv := by sorry

end AlgebraicGeometry
