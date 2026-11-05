/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.ConstructibleReading
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleOrigin
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ConstructibleRetract
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Perfect

/-!
# Bounded constructible complexes with finite condensed coefficients

Let `T` be a finite discrete commutative ring and `Φ = ProEtale.finiteCoefficientDerivedEquivalence`
the identification of complexes of module objects over the condensed ring `T̲` with complexes of
pro-étale sheaves of `T`-modules. A complex `K` of `T̲`-modules is bounded constructible if and
only if `Φ K` is of étale origin, `D(ν^*)` of a bounded constructible étale complex
(`ProEtale.CondensedRing.boundedConstructible_iff_of_finite`). Consequently the bounded
constructible complexes of `T̲`-modules form a triangulated subcategory
(`ProEtale.CondensedRing.isTriangulated_boundedConstructible_of_finite`) which is stable under
retracts (`ProEtale.CondensedRing.boundedConstructible_of_retract_of_finite`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (T : Type) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] [DiscreteTopology T]
  [Finite T] {X : Scheme.{u}}

end AlgebraicGeometry.ProEtale.CondensedRing
