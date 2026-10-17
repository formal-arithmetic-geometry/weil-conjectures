module

public import WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients

universe u
open CategoryTheory Limits AlgebraicGeometry

local instance (X : Scheme.{u}) : EssentiallySmall.{u + 1} X.Etale :=
  have : LocallySmall.{u + 1} X.Etale :=
    @locallySmall_of_univLE X.Etale _ (@univLE_of_max.{u, u + 1} UnivLE.self)
  essentiallySmall_of_small_of_locallySmall _

set_option synthInstance.maxHeartbeats 400000 in
set_option profiler true in
example (X : Scheme.{u}) (Λ : Type (u+1)) [CommRing Λ] :
    HasCountableCoproducts (Sheaf X.smallEtaleTopology (ModuleCat.{u+1} Λ)) := inferInstance

set_option profiler true in
example (X : Scheme.{u}) (Λ : Type (u+1)) [CommRing Λ] :
    IsGrothendieckAbelian.{u+1} (Sheaf X.smallEtaleTopology (ModuleCat.{u+1} Λ)) := inferInstance
set_option profiler true in
example (X : Scheme.{u}) (Λ : Type (u+1)) [CommRing Λ] :
    HasColimitsOfSize.{0,0} (Sheaf X.smallEtaleTopology (ModuleCat.{u+1} Λ)) := inferInstance
