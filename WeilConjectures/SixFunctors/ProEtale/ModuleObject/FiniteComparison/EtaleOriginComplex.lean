/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.Derived
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Comparison

/-!
# Complexes of étale origin with finite coefficients

Let `T` be a finite discrete commutative ring and `Λ = C(-, T)` its condensed ring. An object `C`
of `D(Mod_{Λ_X})` whose image under the finite-coefficient comparison
`Φ = ProEtale.finiteCoefficientDerivedEquivalence` is bounded below of étale origin
(`ProEtale.DerivedCategory.plusEtaleOrigin`, i.e. `Φ C ≅ D(ν^*) N` for a bounded below complex `N`
of étale sheaves of `T`-modules) is represented by a strictly bounded below complex `K` of module
objects each of whose terms is of étale origin: `E (K n) ≅ ν^* F₀ⁿ` for étale sheaves `F₀ⁿ`, where
`E = ProEtale.finiteCoefficientModEquivalence`
(`ProEtale.exists_complex_of_plusEtaleOrigin`).

This is the form in which bounded below complexes of étale origin enter levelwise constructions
(traces, acyclicity) on module objects.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

variable {X : Scheme.{u}} (T : Type) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T]
  [DiscreteTopology T] [Finite T]

end AlgebraicGeometry.ProEtale
