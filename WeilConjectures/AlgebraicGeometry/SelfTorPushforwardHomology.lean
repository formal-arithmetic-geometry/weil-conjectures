/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.KFlat
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import WeilConjectures.AlgebraicGeometry.DerivedTensorStructure
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.AlgebraicGeometry.SelfTorProjectionHomology
public import WeilConjectures.AlgebraicGeometry.SelfTorProjectionHomologyTermwise

/-! # Closed-immersion self-Tor on fixed resolution representatives

Source: Stacks Project, Tags 08EU, 068G, 06YS and 08KS.
(blueprint: lem-pc-self-tor-pushforward-homology). -/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
namespace AlgebraicGeometry

end AlgebraicGeometry
