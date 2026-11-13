/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
import WeilConjectures.Algebra.Homology.KInjectiveRestrictOpen
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.FullyFaithful
import Mathlib.AlgebraicGeometry.Restrict

/-! # Exactness and K-injective preservation for open-immersion restriction

## References

* Stacks Project, Tags 08BS and 01AH.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry


/-- Restriction along any open immersion is exact and preserves K-injective complexes.
(Stacks, Tags 08BS and 01AH) -/
theorem openImmersion_restriction_derived_properties
    {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] :
    PreservesFiniteLimits (Scheme.Modules.restrictFunctor j) ∧
      (Scheme.Modules.restrictFunctor j).PreservesKInjectiveComplexes := by
  classical
  let e := j.isoOpensRange
  let F := Scheme.Modules.restrictFunctor e.hom
  let G := Scheme.Modules.restrictFunctor e.inv
  let : F.IsEquivalence := Functor.IsEquivalence.mk' G
    ((Scheme.Modules.restrictFunctorId).symm ≪≫
      (Scheme.Modules.restrictFunctorCongr e.inv_hom_id).symm ≪≫
      Scheme.Modules.restrictFunctorComp e.inv e.hom)
    ((Scheme.Modules.restrictFunctorComp e.hom e.inv).symm ≪≫
      Scheme.Modules.restrictFunctorCongr e.hom_inv_id ≪≫
      Scheme.Modules.restrictFunctorId)
  let R := SheafOfModules.overFunctor.{u} (moduleRings Y.toRingedSpace) j.opensRange
  let E := (Scheme.Modules.overEquiv j.opensRange).functor
  let : R.Additive := Functor.additive_of_preserves_binary_products _
  let : E.Additive := Functor.additive_of_preserves_binary_products _
  let : R.PreservesKInjectiveComplexes :=
    ⟨fun I _ ↦ kInjective_of_restrict_open Y.toRingedSpace j.opensRange I⟩
  have h : (R ⋙ E) ⋙ F ≅ Scheme.Modules.restrictFunctor j :=
    Functor.isoWhiskerRight (Scheme.Modules.overFunctorEquiv j.opensRange) F ≪≫
      (Scheme.Modules.restrictFunctorComp e.hom j.opensRange.ι).symm ≪≫
      Scheme.Modules.restrictFunctorCongr j.isoOpensRange_hom_ι
  exact ⟨inferInstance, Functor.preservesKInjectiveComplexes_of_iso h⟩

end AlgebraicGeometry
