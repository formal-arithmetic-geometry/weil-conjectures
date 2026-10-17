module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ReductionExtendScalars
public import WeilConjectures.SixFunctors.Etale.Derived.Hom
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients

universe u
open CategoryTheory Limits AlgebraicGeometry

local instance (X : Scheme.{u}) : EssentiallySmall.{u + 1} X.Etale :=
  have : LocallySmall.{u + 1} X.Etale :=
    @locallySmall_of_univLE X.Etale _ (@univLE_of_max.{u, u + 1} UnivLE.self)
  essentiallySmall_of_small_of_locallySmall _

local instance (X : Scheme.{u}) (Λ : Type (u + 1)) [CommRing Λ] :
    HasCountableCoproducts (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
  ⟨fun J _ ↦ (inferInstance : HasColimitsOfSize.{0, 0} (Sheaf X.smallEtaleTopology
    (ModuleCat.{u + 1} Λ))).has_colimits_of_shape _⟩

set_option profiler true in
example (X : Scheme.{u}) (Λ Λ' : Type (u + 1)) [CommRing Λ] [CommRing Λ'] (φ : Λ →+* Λ') :
    Prop := (Sheaf.extendScalars X.smallEtaleTopology φ).PreservesKFlatQuasiIso

example (X : Scheme.{u}) (Λ : Type (u + 1)) [CommRing Λ] : True := by
  let i : MonoidalCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) := inferInstance
  trace_state
  have : i = inferInstance := by unfold i; trace_state; rfl
  trivial
#synth MonoidalCategory (Sheaf (Scheme.smallEtaleTopology (Scheme.Spec (CommRingCat.of ℤ)))
  (ModuleCat.{1} (ULift ℤ)))
