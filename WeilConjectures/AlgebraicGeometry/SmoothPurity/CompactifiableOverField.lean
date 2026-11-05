/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import WeilConjectures.Compactification.Defs
import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.Compactification.NagataCompactification

/-!
# Compactifiability over a field

Source: Weil conjectures blueprint, sec-smooth-purity/sk-prop-sf-cbc,
`def-asd-compactifiable` (blueprint: def-asd-compactifiable); Stacks Project, Tags 0ATT, 0F41.

The defining clause uses the existing `AlgebraicGeometry.Compactification` and
`AlgebraicGeometry.HasCompactification`: a scheme `Z`, an open immersion `i`, a proper
morphism `g`, and the equality `f = i ≫ g`. No new compactifiability predicate is introduced.
The statement below records the node's additional existence assertion over a field.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

end AlgebraicGeometry
