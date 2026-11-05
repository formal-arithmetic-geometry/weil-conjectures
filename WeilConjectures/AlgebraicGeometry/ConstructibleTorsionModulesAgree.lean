/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ConstructibleTorsionCurveSheaf
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import Mathlib.Data.ZMod.Basic
import WeilConjectures.AlgebraicGeometry.FiniteLocalAbelianForget
import WeilConjectures.AlgebraicGeometry.FiniteLocalCyclicModuleForget
import WeilConjectures.AlgebraicGeometry.KilledSheafModuleLift
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.AlgebraicGeometry.TorsionEtaleSheaf
import WeilConjectures.AlgebraicGeometry.TorsionSheafCharacterizations
import WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteStalksComparison

/-!
# Constructibility of torsion abelian sheaves and of cyclic-coefficient module sheaves

Source: Stacks Project, Tags 03RW(2),(3), 095E and 03RU; the comparison is explicit
(blueprint: lem-weil-pbc-constructible-torsion-modules-agree).
-/

@[expose] public section

universe v

open CategoryTheory

namespace AlgebraicGeometry.Scheme

end AlgebraicGeometry.Scheme
