/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.TowerCanonicalKummerComplex

/-! # Exactness of the concrete named Kummer complex -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.SpTowerClasses
attribute [local instance 2000] Abelian.toPreadditive
  Preadditive.preadditiveHasZeroMorphisms

/-- The named actual Kummer complex is short exact. -/
theorem towerKummerShortExact (l : ℕ) [Fact l.Prime] {T : Scheme.{u}} (k : Kummer l T) :
    (towerKummerComplex l k).ShortExact := by
  exact k.exact

end AlgebraicGeometry.ProEtale.SpTowerClasses

attribute [instance high] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
