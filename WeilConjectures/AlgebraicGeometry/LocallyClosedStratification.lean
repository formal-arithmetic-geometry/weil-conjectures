/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import WeilConjectures.Topology.Stratification

/-!
# Blueprint statements

def-constructible-stratification.
-/

@[expose] public section

universe w

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- def-constructible-stratification. -/
structure LocallyClosedStratification (X : Scheme.{w}) extends Topology.Stratification X where
                                          
  domain : Fin n → Scheme.{w}
                                            
  immersion : ∀ i : Fin n, domain i ⟶ X
                                                
  isImmersion : ∀ i : Fin n, IsImmersion (immersion i)
                                                           
  range_immersion : ∀ i : Fin n, Set.range (immersion i) = stratum i

end AlgebraicGeometry.Scheme
