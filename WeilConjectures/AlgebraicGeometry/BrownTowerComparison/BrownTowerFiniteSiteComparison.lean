/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.BrownTowerComparison.BrownTowerBoundedTransport

import WeilConjectures.AlgebraicGeometry.BrownTowerComparison.BrownTowerGeometricTransport
import WeilConjectures.CategoryTheory.Exact.ExactDerivedAdjunctionBounds
import Mathlib.CategoryTheory.HomCongr
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Finite evaluation and bounded site transport

Source: integral-adjunction proof, first Hom display; Zheng Lemmas 4.10, 5.16, 5.22
(blueprint: lem-pur-brown-tower-finite-site-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genCtorIdx false
set_option genSizeOf false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u a av b bv x xv y yv
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite SheafOfModules
namespace AlgebraicGeometry
namespace BrownTowerComparison

section CategoricalTransport
variable {A : Type a} [Category.{av} A] {B : Type b} [Category.{bv} B]
  {X : Type x} [Category.{xv} X] {Y : Type y} [Category.{yv} Y]
  {F : A ⥤ B} {G : B ⥤ A} (adj : F ⊣ G)
  {U : A ⥤ X} {V : X ⥤ A} (ax : U ⊣ V)
  {W : B ⥤ Y} {Z : Y ⥤ B} (ay : W ⊣ Z)
  (P : X ⥤ Y) (d : F ⋙ W ⟶ U ⋙ P)

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
end CategoricalTransport

section BuildTransport
attribute [local instance 5000] proSystemDerived proLevelDerived
  strictEtaleSystemDerived strictEtaleLevelDerived
variable {O : Type (u + 1)} [CommRing O] {t : O}
  {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f}
  {S : StrictEtaleCompactSupport.{u} O t c} {G : EtaleTowerBrownAdjunction.{u} S}
  {H : FiniteEvaluation.{u} S G}

end BuildTransport

end BrownTowerComparison
end AlgebraicGeometry
