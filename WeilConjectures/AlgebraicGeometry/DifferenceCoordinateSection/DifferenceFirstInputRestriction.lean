/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineDifferenceTower.AffineDifferenceTowerFactorization
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleNormalization.FiniteEtaleDualizingNormalization
import WeilConjectures.AlgebraicGeometry.DualizingLocality.DualizingSigmaCocycleLocality
import all WeilConjectures.AlgebraicGeometry.Section.SectionExceptionalFibreCoherence

/-! # Difference-coordinate first input restriction

Source: composition coherence Step 1
(blueprint: lem-pur-difference-first-input-restriction).
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.ProEtale.DifferenceCoordinateSection
open WeilConjectures.PurityFiniteSetting.DiagonalPasting
open AlgebraicGeometry.AffineDifferenceTower
open FiniteEtaleNormalization

/-- The raw dualizing base-change composition law with named composite arrows. Substitute those
names and apply the existing mate-pasting calculation.
Source: composition coherence Step 1 (blueprint: lem-pur-difference-first-input-restriction). -/
private theorem dualizing_base_comp_named
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X X' X'' Y Y' Y'' : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian X'] [IsNoetherian X'']
    [IsNoetherian Y] [IsNoetherian Y'] [IsNoetherian Y'']
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {f'' : X'' ⟶ Y''}
    {v : Y' ⟶ Y} {w : Y'' ⟶ Y'} {v' : X' ⟶ X} {w' : X'' ⟶ X'}
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [HasCompactification f] [HasCompactification f'] [HasCompactification f'']
    [QuasiCompact f'] [QuasiCompact f'']
    (sq₁ : IsPullback v' f' f v) (sq₂ : IsPullback w' f'' f' w)
    (a : X'' ⟶ X) (b : Y'' ⟶ Y) (ha : a = w' ≫ v') (hb : b = w ≫ v)
    (sq : IsPullback a f'' f b) :
    Etale.dualizingComplexBaseChangeMap A sq =
      (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} A) w' v' a ha).hom.app
        (Etale.dualizingComplex A f) ≫
      (Etale.upperStar (ModuleCat.{u + 1} A) w').leftDerivedFunctor.map
        (Etale.dualizingComplexBaseChangeMap A sq₁) ≫
      Etale.dualizingComplexBaseChangeMap A sq₂ := by
  subst a
  subst b
  exact Etale.dualizing_base_comp A sq₁ sq₂

end AlgebraicGeometry.ProEtale.DifferenceCoordinateSection
