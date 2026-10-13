module

public import Sheaf.Paper.ModuleCupRealizationComplexData
public import Sheaf.Paper.ModuleCupNaiveDerivedCompatibility

@[expose] public section

universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules
noncomputable section

/-- The derived homology class represented by a localized cycle.
Source: Stacks Project, Tag 0FKU.
(blueprint: new-module-cup-derived-homology-tensor)
-/
def cupLocalizedCycleClass {k : Type u} [CommRing k]
    [HasDerivedCategory.{u} (ModuleCat.{u} k)] (K : CochainComplex (ModuleCat.{u} k) ℤ)
    (n : ℤ) (z : K.cycles n) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} k) n).obj (DerivedCategory.Q.obj K) :=
  ((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} k) n).app K).inv
    (K.homologyπ n z)

end
end AlgebraicGeometry.Scheme.Modules
