module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperLowerStar

@[expose] public section

universe u

open CategoryTheory Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

variable (X : Scheme.{u}) (T : Type) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T]
  [DiscreteTopology T] [Finite T]

instance additive_finiteCoefficientModEquivalence_functor :
    (finiteCoefficientModEquivalence X T).functor.Additive :=
  Functor.additive_of_preserves_binary_products _

/-- The derived version of `finiteCoefficientModEquivalence`. -/
noncomputable def finiteCoefficientDerivedEquivalence :
    DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (Profinite.continuousMapRingObj T) X)) ≌
      DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1} T))) :=
  (finiteCoefficientModEquivalence X T).mapDerivedCategory

end AlgebraicGeometry.ProEtale
