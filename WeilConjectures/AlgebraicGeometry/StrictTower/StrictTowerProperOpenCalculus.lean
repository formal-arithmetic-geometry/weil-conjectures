/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.StrictTower.FiniteConstantCoefficientTransport
public import WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerProperOpenArrows
public import WeilConjectures.AlgebraicGeometry.Proper.Open.ProperOpenInterchangeCoherence
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.AlgebraicGeometry.StrictTower.ProperOpenClopenProjector
import WeilConjectures.AlgebraicGeometry.StrictTower.ProperOpenAlphaPasting
import WeilConjectures.AlgebraicGeometry.StrictTower.MateEvaluationScalars.TowerMateEvaluationScalars
import WeilConjectures.AlgebraicGeometry.StrictTower.SingleLevelFiniteProperOpenTransport
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerPullbackSquarePasting
import Mathlib.CategoryTheory.Adjunction.Triple
import all WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
import WeilConjectures.AlgebraicGeometry.ProEtale.Ringed.ProEtaleRingedOpenComparison
import WeilConjectures.Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-!
# Normalized proper/open calculus on strict pro-etale towers

Source: Stacks Project, Tags 0F7B, 0F7C, 0F7D, 0F7F, 07A7 and 09AE, and the explicit
strict-tower refinement in the blueprint (blueprint: lem-cbc-strict-tower-proper-open-calculus).

The index `n : ℕ` denotes positive level `n+1`. All derived categories below localize
complexes of strict towers, rather than forming towers in separate derived categories.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency.types false

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale.StrictTower

variable (B : Type (u + 1)) [CommRing B]

attribute [local instance] clopenTowerAbelian

section PullbackUnits
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] Scheme.proEtaleRingModuleAdjunction moduleRComp moduleRId

@[irreducible] private noncomputable def moduleAdj {X Y : Scheme.{u}} (f : X ⟶ Y) :
    modulePullback B f ⊣ moduleDirectImage B f :=
  Scheme.proEtaleRingModuleAdjunction f (coefficients B Y) (coefficients B X)
    (constantRingIso B f)

@[irreducible] private noncomputable def moduleGId (X : Scheme.{u}) :
    modulePullback B (𝟙 X) ≅ 𝟭 (Modules B X) :=
  Adjunction.leftAdjointIdIso
    (Scheme.proEtaleRingModuleAdjunction (𝟙 X) (coefficients B X)
      (coefficients B X) (constantRingIso B (𝟙 X))) (moduleRId B X)

@[irreducible] private noncomputable def towerGId (X : Scheme.{u}) :
    towerPullback B (𝟙 X) ≅ 𝟭 (Towers B X) :=
  (Functor.whiskeringRight ℕᵒᵖ _ _).mapIso (moduleGId B X) ≪≫
    Functor.whiskeringRightObjIdIso

attribute [local irreducible] moduleGComp

attribute [local irreducible] gComp gId towerGComp adj jAdj G R J alpha

end PullbackUnits

section NormalizedIdentities
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] gComp gId adj jAdj G R J alpha

end NormalizedIdentities

/-- The finite etale comparison furnished by the dependency's section and derived-unit
normalizations; these determine its arrow, including the refinement case.
Source: Stacks, Tag 0F7B
(blueprint: lem-cbc-strict-tower-proper-open-calculus). -/
@[no_expose] noncomputable def finiteGamma (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S) (p : W ⟶ T) (i : S ⟶ T)
    [IsOpenImmersion k] [IsOpenImmersion i] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i) :
    Etale.rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) r ⋙
        (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i).mapDerivedCategoryPlus ≅
      (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k).mapDerivedCategoryPlus ⋙
        Etale.rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) p :=
  secondWitness (Etale.properOpenInterchangeCoherence Λ) k i r p h

attribute [local irreducible] finiteSource finiteTarget

section GammaIdentities
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] adj jAdj G R J alpha gComp gId jId

end GammaIdentities

end AlgebraicGeometry.ProEtale.StrictTower
