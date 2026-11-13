/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CartesianHigherImageTransitions
public import WeilConjectures.AlgebraicGeometry.AbelianHigherDirectImageClassCompatibility
public import WeilConjectures.AlgebraicGeometry.CartesianHigherImageChartSystem
public import WeilConjectures.AlgebraicGeometry.RestrictedOverAbelianComplexData
import WeilConjectures.AlgebraicGeometry.CartesianChartExchangeNaturality

/-! # Chart cohomology and cartesian exchange

Source: Stacks Project, Tag 0EYM, second proof, canonical cohomology comparisons.
-/

@[expose] public section

universe u
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale

noncomputable local instance (T : Scheme.{u}) :
    HasShift (DerivedCategory.Plus (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})) ℤ :=
  inferInstance

/-- Restricted chart cohomology compares with cartesian derived Hom, compatibly
with the prescribed exchange map. This is a map comparison, without continuity,
representatives, a limiting cone, affineness, qcqs hypotheses or filteredness
(Stacks, Tags 0EYM, 03Q8, 03CB and 09YQ). -/
theorem exists_cartesianChart_cohomology_comparison
    {S X : Scheme.{u}} (f : X ⟶ S)
    {I : Type u} [SmallCategory I] (D : I ⥤ Over S) (c : Cone D)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ)
    (i : I) (V : (D.obj i).left.Etale) (U : c.pt.left.Etale)
    (r : U.left ⟶ V.left)
    (hr : IsPullback r U.hom V.hom (c.π.app i).left) :
    let h := pullback.snd f (D.obj i).hom
    let Fᵢ := (upperStar AddCommGrpCat.{u + 1} (pullback.fst f (D.obj i).hom)).obj F
    let E := cartesianChartDiagram f D i
    let d := cartesianChartCone f D c i
    ∃ (e : restrictedOverCohomology h Fᵢ (q : ℤ) d.pt V ≅ AddCommGrpCat.of
        ((DerivedCategory.Plus.singleFunctor _ 0).obj
          ((abelianComparisonFree c.pt.left).obj U) ⟶
            (cartesianDerivedImage f c.pt.hom
              ((DerivedCategory.Plus.singleFunctor _ 0).obj F))⟦(q : ℤ)⟧))
      (lift : ∀ j : Over i, restrictedOverCohomology h Fᵢ (q : ℤ) (E.obj j) V →
        ((DerivedCategory.Plus.singleFunctor _ 0).obj
          ((abelianComparisonFree c.pt.left).obj U) ⟶
            ((D+(((c.π.app j.left).left)^*[AddCommGrpCat.{u + 1}])).obj
              (cartesianDerivedImage f (D.obj j.left).hom
                ((DerivedCategory.Plus.singleFunctor _ 0).obj F)))⟦(q : ℤ)⟧)),
      ∀ (j : Over i) (x : restrictedOverCohomology h Fᵢ (q : ℤ) (E.obj j) V),
        lift j x ≫ (shiftFunctor _ (q : ℤ)).map
          (cartesianDerivedImageMap f (D.obj j.left).hom c.pt.hom
            (c.π.app j.left).left (Over.w (c.π.app j.left)).symm
              ((DerivedCategory.Plus.singleFunctor _ 0).obj F)) =
          e.hom (restrictedOverCohomologyMap h Fᵢ (q : ℤ) (d.π.app j) V x) := by
  refine ⟨cartesianChartCohomologyIso f (D.obj i).hom (c.π.app i).left c.pt.hom
    (Over.w (c.π.app i)).symm F q V U r hr,
    cartesianChartCohomologyLift f D c F q i V U r hr, ?_⟩
  intro j x
  exact cartesianChartCohomologyLift_exchange f D c F q i V U r hr j x

end AlgebraicGeometry.Etale
