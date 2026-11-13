/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.RingTheory.Unramified.LocalStructure

/-!
# Discreteness of a scheme unramified over a field

## References

* [Stacks Project, Tag 02G7](https://stacks.math.columbia.edu/tag/02G7)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A scheme unramified over a field has discrete underlying topological space. -/
theorem discreteTopology_of_unramified_over_field {k : Type u} [Field k]
    {Y : Scheme.{u}} (g : Y ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType g] [IsOpenImmersion (pullback.diagonal g)] :
    DiscreteTopology Y := by
  have : LocallyQuasiFinite g := by
    constructor
    intro U hU V hV e
    let := (g.appLE U V e).hom.toAlgebra
    have : Algebra.FiniteType Γ(Spec (CommRingCat.of k), U) Γ(Y, V) :=
      g.finiteType_appLE hU hV e
    have : Algebra.FormallyUnramified Γ(Spec (CommRingCat.of k), U) Γ(Y, V) :=
      g.formallyUnramified_appLE hU hV e
    exact (inferInstance : Algebra.QuasiFinite Γ(Spec (CommRingCat.of k), U) Γ(Y, V))
  have : IsLocallyArtinian Y := .of_locallyQuasiFinite g
  infer_instance

end AlgebraicGeometry
