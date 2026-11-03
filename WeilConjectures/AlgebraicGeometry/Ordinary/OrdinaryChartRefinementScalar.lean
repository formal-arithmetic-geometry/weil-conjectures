/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactScalarCoherence
import all WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactScalarCoherence
import all WeilConjectures.AlgebraicGeometry.Proper.Open.ProperOpenCoefficientRefinement
import WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange

/-! # Unbounded scalar compatibility of compactification refinement

Source: blueprint smooth-purity reduction, Charts.
(blueprint: lem-pur-ordinary-chart-refinement-scalar).
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale
set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2
attribute [local irreducible] Functor.leftAdjoint Functor.rightAdjoint
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor Functor.mapDerivedCategory
  upperStar lowerStar

private theorem refinement_normalization_unbounded
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} {c d : Compactification f}
    (r : c.Refinement d) (hp : IsPullback c.i (𝟙 X) r.hom d.i)
    (K : DerivedCategoryModule A X) :
    (derivedOpenImmersionLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} A) d.i).homEquiv _ _
      ((mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) r.hom).unit.app
        ((openImmersionLowerShriek (ModuleCat.{u + 1} A) d.i).mapDerivedCategory.obj K) ≫
      (rightDerivedLowerStar (ModuleCat.{u + 1} A) r.hom).map
        ((refinementLowerShriekBaseChangeDerivedIso (ModuleCat.{u + 1} A) r hp).inv.app K)) ≫
      (refinementRestriction A r.hom c.i d.i r.i_hom).app
        ((openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategory.obj K) =
      (derivedOpenImmersionLowerShriekUpperStarAdjunction
        (ModuleCat.{u + 1} A) c.i).unit.app K := by
  have h := refinement_transpose_normalization
    (openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategory
    (upperStar (ModuleCat.{u + 1} A) c.i).mapDerivedCategory
    (openImmersionLowerShriek (ModuleCat.{u + 1} A) d.i).mapDerivedCategory
    (upperStar (ModuleCat.{u + 1} A) d.i).mapDerivedCategory
    (upperStar (ModuleCat.{u + 1} A) r.hom).mapDerivedCategory
    (rightDerivedLowerStar (ModuleCat.{u + 1} A) r.hom)
    (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) c.i)
    (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) d.i)
    (mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) r.hom)
    (Functor.mapDerivedCategoryTriangleIso
      (upperStarCompIso (ModuleCat.{u + 1} A) c.i r.hom d.i r.i_hom))
    (refinementLowerShriekBaseChangeDerivedIso (ModuleCat.{u + 1} A) r hp)
    (unit_map_refinementLowerShriekBaseChangeDerivedIso (ModuleCat.{u + 1} A) r hp) K
  simpa only [refinementRestriction, upperStarCompIso_eq,
    Functor.mapDerivedCategoryTriangleIso, mapDerivedUpperStarLowerStarAdjunction_eq,
    rightDerivedLowerStar] using h

private theorem refinement_open_scalar_unbounded
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    {f : X ⟶ Y} {c d : Compactification f}
    (r : c.Refinement d) (hp : IsPullback c.i (𝟙 X) r.hom d.i)
    (K : DerivedCategoryModule A X) :
    let αA := (mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) r.hom).unit.app
      ((openImmersionLowerShriek (ModuleCat.{u + 1} A) d.i).mapDerivedCategory.obj K) ≫
        (rightDerivedLowerStar (ModuleCat.{u + 1} A) r.hom).map
          ((refinementLowerShriekBaseChangeDerivedIso (ModuleCat.{u + 1} A) r hp).inv.app K)
    let αB := (mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) r.hom).unit.app
      ((openImmersionLowerShriek (ModuleCat.{u + 1} B) d.i).mapDerivedCategory.obj
        ((scalarExtension φ X).obj K)) ≫
        (rightDerivedLowerStar (ModuleCat.{u + 1} B) r.hom).map
          ((refinementLowerShriekBaseChangeDerivedIso (ModuleCat.{u + 1} B) r hp).inv.app
            ((scalarExtension φ X).obj K))
    (scalarExtension φ d.Z).map αA ≫
      (scalarMate φ r.hom).app
        ((openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategory.obj K) ≫
      (rightDerivedLowerStar (ModuleCat.{u + 1} B) r.hom).map
        (properOpenCoefficientOpenIso φ c.i K).hom =
      (properOpenCoefficientOpenIso φ d.i K).hom ≫ αB := by
  dsimp only
  have : IsLocallyNoetherian c.Z := LocallyOfFiniteType.isLocallyNoetherian c.g
  have : CompactSpace c.Z := QuasiCompact.compactSpace_of_compactSpace c.g
  have : IsNoetherian c.Z := ⟨⟩
  have : IsLocallyNoetherian d.Z := LocallyOfFiniteType.isLocallyNoetherian d.g
  have : CompactSpace d.Z := QuasiCompact.compactSpace_of_compactSpace d.g
  have : IsNoetherian d.Z := ⟨⟩
  let kA := Functor.mapDerivedCategoryNatIso
      (upperStarComp (ModuleCat.{u + 1} A) c.i r.hom d.i r.i_hom.symm) ≪≫
    Functor.mapDerivedCategoryCompIso _ _
  let kB := Functor.mapDerivedCategoryNatIso
      (upperStarComp (ModuleCat.{u + 1} B) c.i r.hom d.i r.i_hom.symm) ≪≫
    Functor.mapDerivedCategoryCompIso _ _
  have hχ : ∀ M : DerivedCategoryModule A c.Z,
      (upperStar (ModuleCat.{u + 1} B) d.i).mapDerivedCategory.map
          ((scalarMate φ r.hom).app M) ≫
        (refinementRestriction B r.hom c.i d.i r.i_hom).app ((scalarExtension φ c.Z).obj M) ≫
        (properOpenCoefficientPullbackIso φ c.i).hom.app M =
      (properOpenCoefficientPullbackIso φ d.i).hom.app
          ((rightDerivedLowerStar (ModuleCat.{u + 1} A) r.hom).obj M) ≫
        (scalarExtension φ X).map ((refinementRestriction A r.hom c.i d.i r.i_hom).app M) := by
    intro M
    simpa only [refinementRestriction, kA, kB, rightDerivedLowerStar,
      Functor.map_comp, Category.assoc] using
      restriction_coefficient_mate
        ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) r.hom).ofNatIsoLeft
          (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) r.hom))
        ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) r.hom).ofNatIsoLeft
          (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} B) r.hom))
        (upperStar (ModuleCat.{u + 1} A) c.i).mapDerivedCategory
        (upperStar (ModuleCat.{u + 1} A) d.i).mapDerivedCategory
        (upperStar (ModuleCat.{u + 1} B) c.i).mapDerivedCategory
        (upperStar (ModuleCat.{u + 1} B) d.i).mapDerivedCategory
        (scalarExtension φ X) (scalarExtension φ c.Z) (scalarExtension φ d.Z)
        kA kB (properOpenCoefficientPullbackIso φ c.i)
        (properOpenCoefficientPullbackIso φ d.i) (properOpenCoefficientPullbackIso φ r.hom)
        (scalarMate φ r.hom) (coefficientMate_counit φ r.hom)
        (coefficientPullback_comp φ r.hom c.i d.i r.i_hom) M
  have hA := refinement_normalization_unbounded A r hp K
  have hB := refinement_normalization_unbounded B r hp ((scalarExtension φ X).obj K)
  have hα : IsIso ((mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B)
      r.hom).unit.app
      ((openImmersionLowerShriek (ModuleCat.{u + 1} B) d.i).mapDerivedCategory.obj
        ((scalarExtension φ X).obj K))) :=
    isIso_mapDerivedUpperStarLowerStarAdjunction_unit_app_openImmersionLowerShriek
      r B hp ((scalarExtension φ X).obj K)
  have ht : IsIso ((refinementRestriction B r.hom c.i d.i r.i_hom).app
      ((openImmersionLowerShriek (ModuleCat.{u + 1} B) c.i).mapDerivedCategory.obj
        ((scalarExtension φ X).obj K))) := by
    have hi : IsIso ((derivedOpenImmersionLowerShriekUpperStarAdjunction
        (ModuleCat.{u + 1} B) d.i).homEquiv ((scalarExtension φ X).obj K) _
        ((mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) r.hom).unit.app
          ((openImmersionLowerShriek (ModuleCat.{u + 1} B) d.i).mapDerivedCategory.obj
            ((scalarExtension φ X).obj K)) ≫
          (rightDerivedLowerStar (ModuleCat.{u + 1} B) r.hom).map
            ((refinementLowerShriekBaseChangeDerivedIso (ModuleCat.{u + 1} B) r hp).inv.app
              ((scalarExtension φ X).obj K)))) := by
      simp only [Adjunction.homEquiv_unit, rightDerivedLowerStar]
      infer_instance
    exact IsIso.of_isIso_fac_left hB
  exact coefficient_refinement_of_restriction
    (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) c.i)
    (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) d.i)
    (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} B) c.i)
    (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} B) d.i)
    (rightDerivedLowerStar (ModuleCat.{u + 1} A) r.hom)
    (rightDerivedLowerStar (ModuleCat.{u + 1} B) r.hom)
    (scalarExtension φ X) (scalarExtension φ c.Z) (scalarExtension φ d.Z)
    (refinementRestriction A r.hom c.i d.i r.i_hom)
    (refinementRestriction B r.hom c.i d.i r.i_hom)
    (properOpenCoefficientPullbackIso φ c.i) (properOpenCoefficientPullbackIso φ d.i)
    (scalarMate φ r.hom) hχ K _ _
    (properOpenCoefficientOpenIso φ c.i K) (properOpenCoefficientOpenIso φ d.i K)
    (coefficientOpen_unit φ c.i K) (coefficientOpen_unit φ d.i K) hA hB

/-- Unbounded scalar compatibility of compactification refinement.
Source: blueprint smooth-purity reduction, Charts.
(blueprint: lem-pur-ordinary-chart-refinement-scalar).

Proof: Express the refinement comparison as inverse proper/open exchange followed by the proper
counit. This identification holds on arbitrary complexes by the published derived normalization
and the open unit equation.
Compute scalar compatibility after restriction to the source open, using the coefficient
base-change cube, the open-unit identities and the counit mate equation. Cancel the invertible
base-change components and transpose back.
Paste this normalized open comparison with the proper scalar mate and apply naturality; the two
compact-support refinement paths agree. No boundedness hypothesis occurs in these computations. -/
theorem ordinaryChartRefinementScalar
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    [Finite A] [Finite B] (φ : A →+* B) {X Y : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian Y] {f : X ⟶ Y} {c d : Compactification f}
    (r : c.Refinement d) (hp : IsPullback c.i (𝟙 X) r.hom d.i)
    (M : DerivedCategoryModule A X) :
    (scalarExtension φ Y).map
        ((rightDerivedLowerShriekOfCompactificationComparison (ModuleCat.{u + 1} A)
          r hp).app M) ≫ (compactScalarMap φ c).app M =
      (compactScalarMap φ d).app M ≫
        (rightDerivedLowerShriekOfCompactificationComparison (ModuleCat.{u + 1} B)
          r hp).app ((scalarExtension φ X).obj M) := by
  have : IsLocallyNoetherian c.Z := LocallyOfFiniteType.isLocallyNoetherian c.g
  have : CompactSpace c.Z := QuasiCompact.compactSpace_of_compactSpace c.g
  have : IsNoetherian c.Z := ⟨⟩
  have : IsLocallyNoetherian d.Z := LocallyOfFiniteType.isLocallyNoetherian d.g
  have : CompactSpace d.Z := QuasiCompact.compactSpace_of_compactSpace d.g
  have : IsNoetherian d.Z := ⟨⟩
  let αA := (mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) r.hom).unit.app
    ((openImmersionLowerShriek (ModuleCat.{u + 1} A) d.i).mapDerivedCategory.obj M) ≫
      (rightDerivedLowerStar (ModuleCat.{u + 1} A) r.hom).map
        ((refinementLowerShriekBaseChangeDerivedIso (ModuleCat.{u + 1} A) r hp).inv.app M)
  let αB := (mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) r.hom).unit.app
    ((openImmersionLowerShriek (ModuleCat.{u + 1} B) d.i).mapDerivedCategory.obj
      ((scalarExtension φ X).obj M)) ≫
      (rightDerivedLowerStar (ModuleCat.{u + 1} B) r.hom).map
        ((refinementLowerShriekBaseChangeDerivedIso (ModuleCat.{u + 1} B) r hp).inv.app
          ((scalarExtension φ X).obj M))
  let kA := Functor.rightDerivedFunctorCompIso' (lowerStar (ModuleCat.{u + 1} A) r.hom)
    (lowerStar (ModuleCat.{u + 1} A) d.g) (refinementLowerStarComp (ModuleCat.{u + 1} A) r)
  let kB := Functor.rightDerivedFunctorCompIso' (lowerStar (ModuleCat.{u + 1} B) r.hom)
    (lowerStar (ModuleCat.{u + 1} B) d.g) (refinementLowerStarComp (ModuleCat.{u + 1} B) r)
  have heA : (rightDerivedLowerShriekOfCompactificationComparison
      (ModuleCat.{u + 1} A) r hp).app M =
      (rightDerivedLowerStar (ModuleCat.{u + 1} A) d.g).map αA ≫
        kA.hom.app
          ((openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategory.obj M) := by
    simp only [rightDerivedLowerShriekOfCompactificationComparison, NatTrans.comp_app,
      Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.comp_map,
      ← Functor.map_comp_assoc]
    rfl
  have heB : (rightDerivedLowerShriekOfCompactificationComparison
      (ModuleCat.{u + 1} B) r hp).app ((scalarExtension φ X).obj M) =
      (rightDerivedLowerStar (ModuleCat.{u + 1} B) d.g).map αB ≫
        kB.hom.app
          ((openImmersionLowerShriek (ModuleCat.{u + 1} B) c.i).mapDerivedCategory.obj
            ((scalarExtension φ X).obj M)) := by
    simp only [rightDerivedLowerShriekOfCompactificationComparison, NatTrans.comp_app,
      Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.comp_map,
      ← Functor.map_comp_assoc]
    rfl
  have ho := refinement_open_scalar_unbounded φ r hp M
  have hc (N : DerivedCategoryModule A c.Z) :
      (scalarExtension φ Y).map (kA.hom.app N) ≫ (scalarMate φ c.g).app N =
        (scalarMate φ d.g).app ((rightDerivedLowerStar (ModuleCat.{u + 1} A) r.hom).obj N) ≫
          (rightDerivedLowerStar (ModuleCat.{u + 1} B) d.g).map ((scalarMate φ r.hom).app N) ≫
          kB.hom.app ((scalarExtension φ c.Z).obj N) := by
    dsimp only [kA, kB]
    rw [refinementLowerStarComp_eq, refinementLowerStarComp_eq]
    exact scalarMate_directImage_composition_eq φ r.hom d.g c.g r.hom_g.symm N
  dsimp only [rightDerivedLowerStar] at *
  rw [heA, heB]
  dsimp only [compactScalarMap, ExceptionalCoefficients.compactSupportMap,
    rightDerivedLowerShriekOfCompactification, Functor.comp_obj]
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hc]
  have hn := (scalarMate φ d.g).naturality αA
  dsimp only [Functor.comp_map, rightDerivedLowerStar] at hn
  erw [reassoc_of% hn]
  have hk := kB.hom.naturality ((ExceptionalCoefficients.openIso φ c.i).hom.app M)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hk
  erw [← hk]
  simp only [← Functor.map_comp_assoc]
  have heq {T : Scheme.{u}} (j : X ⟶ T) [IsOpenImmersion j] :
      (ExceptionalCoefficients.openIso φ j).hom.app M =
        (properOpenCoefficientOpenIso φ j M).hom := by
    have h : ((ExceptionalCoefficients.openIso φ j).app M).symm =
        (properOpenCoefficientOpenIso φ j M).symm := by
      apply Iso.ext
      exact compactScalarOpen_normalization φ j M
    exact congrArg (fun e ↦ e.inv) h
  rw [heq c.i, heq d.i]
  exact congrArg (fun z ↦ (scalarMate φ d.g).app _ ≫
    (rightDerivedLowerStar (ModuleCat.{u + 1} B) d.g).map z ≫
      kB.hom.app _) ho

end AlgebraicGeometry.Etale
