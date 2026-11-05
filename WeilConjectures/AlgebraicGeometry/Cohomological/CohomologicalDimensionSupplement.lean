/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek

/-!
# Torsion étale cohomological dimension

Source: literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-sf-cbc/
def-sc-etale-torsion-cd.md (blueprint: def-sc-etale-torsion-cd).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}}

end AlgebraicGeometry.Scheme

end
