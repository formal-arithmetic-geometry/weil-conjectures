/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ProfiniteCondensedRing
public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LeftDerivedExactComparison
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.CategoryTheory.DerivedCategory.Shift.ExactFunctor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal

/-!
# Canonical shifts and compositors of derived module functors

Source: Stacks, derived.tex, Tags 014X, 015F and 05SE; blueprint
`det-thm-sfb-proper-base-change-rational`, proof paragraph (3)
(blueprint: lem-sfb-module-derived-functor-compositor-shifts).

The pullback shifts are transported from exact termwise pullback by the canonical
counit comparison. The pushforward shifts are the published K-injective shifts.
All comparisons use the actual specified module-object functors and compositors.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ] {X Y Z : Scheme.{u}} (f : X ⟶ Y)

/-- The canonical exact comparison for the specified K-flat module pullback.
Source: Stacks Tag 015F and `def-sfb-left-derived-exact`
(blueprint: lem-sfb-module-derived-functor-compositor-shifts). -/
def modulePullbackExactComparison :
    (moduleObjectDerivedPullback Λ f) ≅ (upperStar Λ f).mapDerivedCategory :=
  (upperStar Λ f).leftDerivedExactComparison
    (upperStar Λ f).leftDerivedFunctor (upperStar Λ f).leftDerivedFunctorCounit

/-- The specified integer shifts on derived module pullback, transported along `c_f`.
Source: Stacks Tags 014X and 015F; node proof step 1
(blueprint: lem-sfb-module-derived-functor-compositor-shifts). -/
instance modulePullbackDerivedCommShift : (moduleObjectDerivedPullback Λ f).CommShift ℤ :=
  Functor.CommShift.ofIso (modulePullbackExactComparison Λ f).symm ℤ

/-- The published K-injective shifts on the named derived module pushforward.
Source: Stacks Tag 05SE and `lem-pc-right-derived-functor-triangulated`
(blueprint: lem-sfb-module-derived-functor-compositor-shifts). -/
instance modulePushforwardDerivedCommShift :
    (moduleObjectDerivedPushforward Λ f).CommShift ℤ :=
  inferInstanceAs ((lowerStar Λ f).rightDerivedFunctor.CommShift ℤ)

/-- The comparison on actual complexes, using localization and exact termwise pullback.
Source: Stacks Tags 014X and 015F; node proof steps 1 and 3
(blueprint: lem-sfb-module-derived-functor-compositor-shifts). -/
def modulePullbackComplexComparison :
    DerivedCategory.Q ⋙ (moduleObjectDerivedPullback Λ f) ≅
      (upperStar Λ f).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q :=
  isoWhiskerLeft DerivedCategory.Q (modulePullbackExactComparison Λ f) ≪≫
    (upperStar Λ f).mapDerivedCategoryFactors

/-- The resolution counit evaluated on a cochain complex, with the canonical localization
and homotopy factorization maps. It is the map used to compute pullback on a K-flat
resolution, and is defined for any complex.
Source: Stacks Tag 05SE; node proof step 3
(blueprint: lem-sfb-module-derived-functor-compositor-shifts). -/
def modulePullbackResolutionCounit
    (M : CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) ℤ) :
    (moduleObjectDerivedPullback Λ f).obj (DerivedCategory.Q.obj M) ⟶
      DerivedCategory.Q.obj ((upperStar Λ f).mapHomologicalComplex (.up ℤ) |>.obj M) :=
  (moduleObjectDerivedPullback Λ f).map
      ((DerivedCategory.quotientCompQhIso _).hom.app M) ≫
    (upperStar Λ f).leftDerivedFunctorCounit.app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj M) ≫
    DerivedCategory.Qh.map
      (((upperStar Λ f).mapHomotopyCategoryFactors (.up ℤ)).hom.app M) ≫
    (DerivedCategory.quotientCompQhIso _).inv.app
      (((upperStar Λ f).mapHomologicalComplex (.up ℤ)).obj M)

private theorem modulePullbackResolutionCounit_eq (M : CochainComplex
    (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) ℤ) :
    modulePullbackResolutionCounit Λ f M =
      (modulePullbackComplexComparison Λ f).hom.app M := by
  have h := congr_app (upperStar Λ f).leftDerivedFunctorIsoMapDerivedCategory_hom_fac
    ((HomotopyCategory.quotient _ (.up ℤ)).obj M)
  dsimp only [whiskerLeft_app, NatTrans.comp_app] at h
  dsimp only [modulePullbackResolutionCounit, modulePullbackComplexComparison,
    Iso.trans_hom, isoWhiskerLeft_hom, NatTrans.comp_app, whiskerLeft_app]
  rw [← h, Functor.mapDerivedCategoryFactorsh_hom_app]
  change (upperStar Λ f).leftDerivedFunctor.map (𝟙 _) ≫
    ((upperStar Λ f).leftDerivedFunctorIsoMapDerivedCategory.hom.app
      (DerivedCategory.Q.obj M) ≫
      ((upperStar Λ f).mapDerivedCategory.map (𝟙 _) ≫
        (upperStar Λ f).mapDerivedCategoryFactors.hom.app M ≫
        𝟙 _ ≫ DerivedCategory.Qh.map (𝟙 _))) ≫
      DerivedCategory.Qh.map (𝟙 _) ≫ 𝟙 _ =
    (upperStar Λ f).leftDerivedFunctorIsoMapDerivedCategory.hom.app
      (DerivedCategory.Q.obj M) ≫
      (upperStar Λ f).mapDerivedCategoryFactors.hom.app M
  simp only [map_id, comp_obj, Category.id_comp, Category.comp_id,
    NatIso.cancel_natIso_hom_left]
  erw [Category.comp_id]

/-- Exactness with precisely the transported pullback shifts and the fixed K-injective
pushforward shifts; compatibility of `c_f` and the termwise comparison with every shift.
Source: Stacks Tags 014X, 015F and 05SE
(blueprint: lem-sfb-module-derived-functor-compositor-shifts).

Proof: (1) `det-prop-sfb-module-pullback-exact-main` makes module pullback exact.
`lem-weil-pbc-exact-functor-derived-factorization` gives the triangulated termwise functor
and its shift-compatible localization comparison. Transport its shift along the canonical
`def-sfb-left-derived-exact` comparison. Images of distinguished triangles are isomorphic
through this comparison, including the connecting arrow, so remain distinguished by TR1
of `def-weil-triangulated-category`. (2) Apply `lem-pc-right-derived-functor-triangulated`
to the additive full module pushforward. Its shifts come from K-injective resolutions:
`lem-weil-pbc-kinjective-shift` permits shifting the resolution itself, and termwise
additivity gives the same differential sign. (3) The counit-compatible exact comparison
commutes with shifts by transport; compose with the shift-compatible termwise
factorization, using `lem-weil-pbc-commshift-nattrans-comp-whisker`. -/
theorem module_derived_functors_exact_and_comparison_shifts :
    (moduleObjectDerivedPullback Λ f).IsTriangulated ∧
      (moduleObjectDerivedPushforward Λ f).IsTriangulated ∧
      NatTrans.CommShift (modulePullbackExactComparison Λ f).hom ℤ ∧
      NatTrans.CommShift (modulePullbackComplexComparison Λ f).hom ℤ := by
  have hs : NatTrans.CommShift (modulePullbackExactComparison Λ f).symm.hom ℤ :=
    Functor.CommShift.ofIso_compatibility (modulePullbackExactComparison Λ f).symm ℤ
  have hc : NatTrans.CommShift (modulePullbackExactComparison Λ f).hom ℤ :=
    NatTrans.CommShift.of_iso_inv (modulePullbackExactComparison Λ f).symm ℤ
  refine ⟨Functor.isTriangulated_of_iso (modulePullbackExactComparison Λ f).symm,
    ?_, hc, ?_⟩
  · exact inferInstanceAs ((lowerStar Λ f).rightDerivedFunctor.IsTriangulated)
  · change NatTrans.CommShift
      (whiskerLeft DerivedCategory.Q (modulePullbackExactComparison Λ f).hom ≫
        (upperStar Λ f).mapDerivedCategoryFactors.hom) ℤ
    infer_instance

variable (g : Y ⟶ Z)

/-- The specified derived compositor, with the named module-functor interfaces.
Source: `prop-sfb-module-left-derived-upper-star-comp`
(blueprint: lem-sfb-module-derived-functor-compositor-shifts). -/
def modulePullbackDerivedCompositor :
    moduleObjectDerivedPullback Λ (f ≫ g) ≅
      moduleObjectDerivedPullback Λ g ⋙ moduleObjectDerivedPullback Λ f :=
  leftDerivedUpperStarComp Λ f g

end AlgebraicGeometry.ProEtale.CondensedRing
