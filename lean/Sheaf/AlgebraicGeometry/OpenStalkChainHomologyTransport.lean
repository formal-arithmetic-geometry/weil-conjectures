/- Copyright (c) 2026 The SHEAF contributors. -/
module
public import Sheaf.AlgebraicGeometry.OpenDerivedStalkIso

/-! # Passing an additive open stalk chain square to derived cohomology -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory CategoryTheory.Limits
noncomputable section
namespace AlgebraicGeometry.SingleComplexBaseChange

/-- An additive chain square induces the corresponding open derived stalk square.

Proof: assemble the degreewise equality as an equality of additive complex maps
and apply homologyMap. Its composition law and naturality of mapHomologyIso move
homology past the forgetful functors. Restriction of scalars followed by forgetting
is the same additive functor as forgetting over the new ring; the canonical
homology comparisons agree, as follows from their universal kernel and cokernel
identities. Expand openDerivedStalkIso and openRestrictionRepresentativeIso.
Their derived restriction comparison factors cancel. The remaining exact-stalk
and exact-restriction homology factors are the homology comparison of the inverse
same-germ stalk map, by naturality of exact-functor homology. Finally apply
comparisonStalkHomologyIso_naturality to alpha and cancel the invertible homology
comparisons at each endpoint. This yields exactly the displayed equality.
No tensor complex or normalized input coordinate is involved. No injectivity,
surjectivity or nonzero condition on the complexes or their homology is used.
Source: Stacks Project, Tags 0098 and 0D5U; Mathlib exact-functor homology
naturality and the localization factorization of exact functors.
(blueprint: lem-pc-open-stalk-chain-homology-transport). -/
theorem openStalk_chain_homology_transport
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {Y Z : Scheme.{u}} (j : Y ⟶ Z) [IsOpenImmersion j] (y : Y) (i : ℤ)
    (N : CochainComplex (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) ℤ)
    (N0 : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
    (V : CochainComplex (ModuleCat.{u} (Z.presheaf.stalk (j y))) ℤ)
    (V0 : CochainComplex (ModuleCat.{u} (Y.presheaf.stalk y)) ℤ)
    (e : Z.presheaf.stalk (j y) ≃+* Y.presheaf.stalk y)
    (t : V ⟶ ((ModuleCat.restrictScalars.{u} e.toRingHom).mapHomologicalComplex
      (.up ℤ)).obj V0)
    (a : V ⟶ ((RingedSpace.moduleStalkFunctor Z.toRingedSpace (j y)).mapHomologicalComplex
      (.up ℤ)).obj N)
    (b : V0 ⟶ ((RingedSpace.moduleStalkFunctor Y.toRingedSpace y).mapHomologicalComplex
      (.up ℤ)).obj N0)
    (alpha : ((Scheme.Modules.restrictFunctor j).mapHomologicalComplex (.up ℤ)).obj N ⟶ N0)
    (h : ∀ k : ℤ,
      (forget₂ (ModuleCat.{u} (Z.presheaf.stalk (j y))) AddCommGrpCat.{u}).map (a.f k) ≫
        (Scheme.Modules.restrictStalkNatIso j y).inv.app (N.X k) ≫
        (forget₂ (ModuleCat.{u} (Y.presheaf.stalk y)) AddCommGrpCat.{u}).map
          ((RingedSpace.moduleStalkFunctor Y.toRingedSpace y).map (alpha.f k)) =
      (forget₂ (ModuleCat.{u} (Z.presheaf.stalk (j y))) AddCommGrpCat.{u}).map (t.f k) ≫
        (forget₂ (ModuleCat.{u} (Y.presheaf.stalk y)) AddCommGrpCat.{u}).map (b.f k)) :
    let F := forget₂ (ModuleCat.{u} (Z.presheaf.stalk (j y))) AddCommGrpCat.{u}
    let F0 := forget₂ (ModuleCat.{u} (Y.presheaf.stalk y)) AddCommGrpCat.{u}
    let HU := comparisonStalkCohomology Y y i ⋙ F0
    F.map (HomologicalComplex.homologyMap t i) ≫
        F.map ((V0.sc i).mapHomologyIso (ModuleCat.restrictScalars.{u} e.toRingHom)).hom ≫
        F0.map (HomologicalComplex.homologyMap b i ≫
          (comparisonStalkHomologyIso Y y N0 i).inv) =
      F.map (HomologicalComplex.homologyMap a i ≫
        (comparisonStalkHomologyIso Z (j y) N i).inv) ≫
        (openDerivedStalkIso j y i).hom.app (DerivedCategory.Q.obj N) ≫
        HU.map ((openRestrictionRepresentativeIso j N).inv ≫ DerivedCategory.Q.map alpha)
    := by sorry

end AlgebraicGeometry.SingleComplexBaseChange
