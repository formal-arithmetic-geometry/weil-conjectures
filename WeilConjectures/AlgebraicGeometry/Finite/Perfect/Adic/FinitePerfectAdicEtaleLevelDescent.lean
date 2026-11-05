/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicEtaleLevelData
import WeilConjectures.AlgebraicGeometry.Finite.Perfect.FinitePerfectChartEtaleOrigin
import WeilConjectures.ConstructibleSheaf.InternalHom
import WeilConjectures.SixFunctors.Etale.Derived.Stability.TorSheaf
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk
import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.ConstantSheaf

/-! # Descent of one finite perfect quotient and its geometric fibre

Source: Stacks Project, Tag 09C6, the construction of L_n and its algebraic fibre;
Tags 09AL, 09B1 and 03Q3.
(blueprint: lem-weil-pbc-finite-perfect-adic-etale-level-descent).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits Opposite ZeroObject
namespace AlgebraicGeometry.Scheme
attribute [local instance] finitePerfectAdicAlgebraDerived
attribute [local instance] finitePerfectModelsAbLocallyBijective

end AlgebraicGeometry.Scheme
