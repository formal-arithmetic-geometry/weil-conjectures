/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CompleteCompactificationLimit.CompleteCompactificationLimitSupport
import all WeilConjectures.CategoryTheory.Diagram.DiagramRingRestrictionPushforward

/-! # Deriving a normalized strict scalar direct-image square
Source: blueprint direct-image proof, paragraph (2).
(blueprint: lem-sp-compactification-scalar-data).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.rightDerivedFunctor
universe u
open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures
namespace AlgebraicGeometry.ProEtale.CompleteCompactificationLimit
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

private theorem normalized_inverse {C : Type*} [Category C] {A B P Q : C}
    (a : A ≅ B) (k : P ≅ Q) (t : B ⟶ P) (s : A ⟶ Q)
    (h : t ≫ k.hom = a.inv ≫ s) : s ≫ k.inv = a.hom ≫ t := by
  apply (cancel_mono k.hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [h, ← Category.assoc, a.hom_inv_id, Category.id_comp]

/-- A strict scalar direct-image square derives with the prescribed unit normalization
once forgotten K-injective complexes compute the fixed-ring image.
Source: Stacks Project, Tags 0D6E and 07A6; blueprint direct-image proof, paragraph (2).
(blueprint: lem-sp-compactification-derived-scalar-comparison).

Proof: apply the universal right-derived comparison to the inverse ordinary square.
Its left unit is scalar forgetting after the simultaneous direct-image unit; its right
unit is fixed-ring direct image after the exact forgetting comparison. Both composites
compute on K-injectives by the stated acyclicity and the canonical resolution unit.
Invert that derived comparison. Multiplying its unit equation by the ordinary square
and canceling its inverse gives exactly IsPushScalarNormalized on every complex. -/
theorem compactificationDerivedScalarComparison
    (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    {Z Y : Scheme.{u}} (p : Z ⟶ Y)
    (DZ : SpCoefficientTowersAbelian l E Z) (DY : SpCoefficientTowersAbelian l E Y)
    (rZ : SpReductionTower l E Z DZ) (rY : SpReductionTower l E Y DY)
    (aZ : LimitPresentation l E Z DZ rZ) (aY : LimitPresentation l E Y DY rY)
    (d₀ : forgetting l E Z DZ ⋙ fixedPushOrd l E p ≅
      ordinaryTowerPush l E b o p ⋙ forgetting l E Y DY)
    (hG : ∀ I : CochainComplex (spCoefficientTowers l E Z) ℤ, I.IsKInjective →
      IsIso ((fixedPushOrd l E p).rightDerivedFunctorUnitQ
        (((forgetting l E Z DZ).mapHomologicalComplex (.up ℤ)).obj I))) :
    ∃ d : forgetDerived l E Z DZ rZ aZ ⋙ (fixedPushOrd l E p).rightDerivedFunctor ≅
      towerPush l E b o p DZ DY ⋙ forgetDerived l E Y DY rY aY,
      IsPushScalarNormalized l E b o p DZ DY rZ rY aZ aY d₀ d := by
  let := DZ.hasDerived
  let := DY.hasDerived
  let := DZ.grothendieck
  let := aZ.additive
  let := aZ.limits
  let := aZ.colimits
  let := aY.additive
  let := aY.limits
  let := aY.colimits
  let F := ordinaryTowerPush l E b o p
  let G := fixedPushOrd l E p
  let x := forgetting l E Z DZ
  let y := forgetting l E Y DY
  let ηF : F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ towerPush l E b o p DZ DY :=
    { app := F.rightDerivedFunctorUnitQ
      naturality := fun {I J} f ↦ F.rightDerivedFunctorUnitQ_naturality f }
  let ηG : G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ G.rightDerivedFunctor :=
    { app := G.rightDerivedFunctorUnitQ
      naturality := fun {I J} f ↦ G.rightDerivedFunctorUnitQ_naturality f }
  obtain ⟨κ, hκ, -⟩ := CategoryTheory.derivedCoefficientComparison
    F G x y (forgetDerived l E Z DZ rZ aZ) (forgetDerived l E Y DY rY aY)
    (forgettingFactors l E Z DZ rZ aZ) (forgettingFactors l E Y DY rY aY)
    (towerPush l E b o p DZ DY) G.rightDerivedFunctor ηF ηG
    (fun I hI ↦ by
      let := hI
      dsimp only [ηF]
      rw [F.rightDerivedFunctorUnitQ_eq]
      infer_instance) hG d₀.symm
  refine ⟨κ.symm, ?_⟩
  intro I
  have hκI := hκ I
  dsimp only [ηF, ηG] at hκI
  change G.rightDerivedFunctorUnitQ ((x.mapHomologicalComplex (.up ℤ)).obj I) ≫
      G.rightDerivedFunctor.map ((forgettingFactors l E Z DZ rZ aZ).inv.app I) ≫
        κ.inv.app (DerivedCategory.Q.obj I) =
    DerivedCategory.Q.map ((NatIso.mapHomologicalComplex d₀ (.up ℤ)).hom.app I) ≫
      (forgettingFactors l E Y DY rY aY).inv.app
        ((F.mapHomologicalComplex (.up ℤ)).obj I) ≫
      (forgetDerived l E Y DY rY aY).map (F.rightDerivedFunctorUnitQ I)
  have hn := normalized_inverse
    (DerivedCategory.Q.mapIso ((NatIso.mapHomologicalComplex d₀ (.up ℤ)).app I))
    (κ.app (DerivedCategory.Q.obj I))
    ((forgettingFactors l E Y DY rY aY).inv.app
      ((F.mapHomologicalComplex (.up ℤ)).obj I) ≫
        (forgetDerived l E Y DY rY aY).map (F.rightDerivedFunctorUnitQ I))
    (G.rightDerivedFunctorUnitQ ((x.mapHomologicalComplex (.up ℤ)).obj I) ≫
      G.rightDerivedFunctor.map ((forgettingFactors l E Z DZ rZ aZ).inv.app I))
    (by
      simpa only [Functor.mapIso_inv, Iso.app_inv, Iso.app_hom,
        NatIso.mapHomologicalComplex, Iso.symm_hom, Category.assoc, F, y] using hκI)
  simpa only [Category.assoc, Functor.mapIso_hom, Iso.app_hom, Iso.app_inv] using hn

end AlgebraicGeometry.ProEtale.CompleteCompactificationLimit
