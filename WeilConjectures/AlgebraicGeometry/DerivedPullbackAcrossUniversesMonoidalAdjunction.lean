/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedPullbackAcrossUniverses
public import WeilConjectures.AlgebraicGeometry.DerivedTensorStructure
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
import WeilConjectures.AlgebraicGeometry.SchemeDerivedStandardEquivalenceMonoidal
import WeilConjectures.AlgebraicGeometry.DerivedPullbackAcrossUniversesLeftDerived
import WeilConjectures.AlgebraicGeometry.DerivedPullbackMonoidalModel
import WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedAdjunctionGeneral

/-! # Monoidal adjunction for the transported derived pullback

Source: Stacks Project, Tags 079U, 079W and 05RU.
-/

@[expose] public section

set_option autoImplicit false

universe u wX wY

open CategoryTheory

namespace AlgebraicGeometry

set_option linter.unusedVariables false in
/-- The transported K-flat pullback is strong monoidal and left adjoint to the
specified K-injective direct image, with independent localization universes
(Stacks, Tags 079U, 079W and 05RU). -/
theorem exists_derivedPullbackAcrossUniverses_monoidal_adjunction
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wY} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))] :
    ∃ m : (derivedPullbackAcrossUniverses f).CoreMonoidal,
      Nonempty (derivedPullbackAcrossUniverses f ⊣ schemeDerivedDirectImage f) := by
  classical
  obtain ⟨mY⟩ := exists_schemeDerivedStandardEquivalence_monoidal Y
  obtain ⟨mX⟩ := exists_schemeDerivedStandardEquivalence_monoidal X
  let := mY.toMonoidal
  let := mX.toMonoidal
  let := (schemeDerivedStandardEquivalence X).inverseMonoidal
  obtain ⟨m, _⟩ := @exists_derivedPullbackMonoidalModel X Y f
    (HasDerivedCategory.standard _) (HasDerivedCategory.standard _)
  let := m.toMonoidal
  obtain ⟨P, hP, hmap, hAdd, L, ε, hL, _, ⟨a⟩⟩ :=
    RingedSpace.derivedModulePullback_adjunction f.toLRSHom.toShHom
  let := hAdd
  obtain ⟨ε', hL'⟩ := exists_derivedPullbackAcrossUniverses_leftDerived f P hP hmap
  let := hL
  let := hL'
  let e := Functor.leftDerivedUnique (derivedPullbackAcrossUniverses f) L ε ε'
    (HomotopyCategory.quasiIso
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ))
  let a' : derivedPullbackAcrossUniverses f ⊣ schemeDerivedDirectImage f :=
    a.ofNatIsoLeft e
  refine ⟨?_, ⟨a'⟩⟩
  change ((schemeDerivedStandardEquivalence Y).functor ⋙
    @derivedPullback X Y f (HasDerivedCategory.standard _)
      (HasDerivedCategory.standard _) ⋙ (schemeDerivedStandardEquivalence X).inverse).CoreMonoidal
  exact Functor.CoreMonoidal.ofLaxMonoidal _

end AlgebraicGeometry
