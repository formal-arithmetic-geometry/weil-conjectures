/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.UpperStarDerived
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleOriginReadingProof
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.EtaleOriginUpperStar

/-!
# Module complexes of étale origin with finite coefficients

Let `T` be a finite discrete commutative ring, `Λ = C(-, T)` and
`Φ = ProEtale.finiteCoefficientDerivedEquivalence` the comparison of `D(Mod_{Λ_X})` with the
derived category of pro-étale sheaves of `T`-modules. We say informally that `C ∈ D(Mod_{Λ_X})`
is *bounded below of étale origin* if `Φ C` is (`ProEtale.DerivedCategory.plusEtaleOrigin`).

* This is stable under derived pullback
  (`ProEtale.plusEtaleOrigin_finiteCoefficientDerivedEquivalence_leftDerivedUpperStar_obj`).
* Bounded constructible complexes with coefficients `𝒪_E/ℓⁿ` on schemes over a field are of étale
  origin (`ProEtale.CondensedRing.plusEtaleOrigin_of_boundedConstructible_integersModPow`).
-/

@[expose] public section

universe u

open CategoryTheory

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

variable (T : Type) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] [DiscreteTopology T]
  [Finite T] {X Y : Scheme.{u}}

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale.CondensedRing

end AlgebraicGeometry.ProEtale.CondensedRing
