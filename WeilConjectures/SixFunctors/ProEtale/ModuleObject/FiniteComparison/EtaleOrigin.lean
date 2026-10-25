/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Constructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.Derived

/-!

# Constructible finite-coefficient module objects are of étale origin

Let `T` be a finite discrete commutative ring and `X` a scheme of finite type over a field. A
bounded complex `K` of module objects over the condensed coefficient ring `T̲_X = p_X^* C(-, T)`
on `X_proét` whose cohomology objects are constructible (`ProEtale.boundedConstructible`, the
intrinsic notion: locally finitely presented, pro-étale locally, on the strata of a finite
stratification) is of étale origin: read as a complex of pro-étale sheaves of `T`-modules
(`ProEtale.finiteCoefficientDerivedEquivalence`), it is isomorphic to `ν^* K'` for a bounded
constructible complex `K'` of étale sheaves of `T`-modules
(`ProEtale.DerivedCategory.boundedConstructible`). This is the input that lets the reduction
modulo `ℓⁿ` of `ℓ`-adic complexes be read on the small étale site.

## Main results

- `ProEtale.isEtaleOrigin_of_isConstructible`: blueprint `lem-sf-proetale-constructible-origin`,
  (ii).

-/

@[expose] public section

universe u

open CategoryTheory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

variable {k : Type u} [Field k] (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom]
  [QuasiCompact X.hom] [IsSeparated X.hom] (T : Type) [TopologicalSpace T] [CommRing T]
  [IsTopologicalRing T] [DiscreteTopology T] [Finite T]

/-- Blueprint `lem-sf-proetale-constructible-origin` (ii) (section `sec-proetale-coefficients`,
`sk-prop-sf-comparison`; the comparison `sk-thm-pe-constructible-comparison`): **constructible
pro-étale complexes with finite coefficients are of étale origin**. For a finite discrete
commutative ring `T` and a scheme `X` of finite type over a field, a bounded complex of module
objects over `T̲_X` with constructible cohomology objects, read as a complex of pro-étale sheaves
of `T`-modules through `finiteCoefficientDerivedEquivalence`, is isomorphic to `ν^* K'` for a
bounded constructible complex `K'` of étale sheaves of `T`-modules
(Bhatt–Scholze, *The pro-étale topology for schemes*, Corollary 5.1.6 and Section 6.8). -/
theorem isEtaleOrigin_of_isConstructible
    (K : BoundedConstructible (condensedRingObj (Profinite.continuousMapRingObj T) X.left)) :
    DerivedCategory.boundedConstructible (ModuleCat.{u + 1} (ULift.{u + 1} T)) X.left
      ((finiteCoefficientDerivedEquivalence X.left T).functor.obj K.obj) :=
  sorry

end AlgebraicGeometry.ProEtale
