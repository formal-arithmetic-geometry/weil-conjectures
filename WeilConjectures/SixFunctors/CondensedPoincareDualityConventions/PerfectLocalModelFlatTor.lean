/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.ProEtaleFiniteProjectiveDualizable
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel

/-! # Flatness and Tor amplitude of finite locally projective coefficients

A component of the local finite projective model proposition. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing

namespace WeilConjectures.CondensedPoincareDualityConventions

/-- The flat and Tor-amplitude part of the local finite projective model.
Source: Stacks Tags 08JJ and 0GN1; the finite-retract argument in the proof of
`prop-pod-perfect-local-model` (blueprint: lem-pod-perfect-local-model-flat-tor).
The local retract is dualizable, hence flat; a degree-zero flat object has Tor
amplitude `[0,0]`, which immediately gives finite Tor amplitude. -/
theorem perfect_local_model_flat_tor
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (S : Scheme.{u})
    (P : supportModules Λ S) (hP : IsFiniteLocallyProjective Λ S P) :
      ObjectProperty.flat P ∧
      DerivedCategory.torAmplitudeIn (supportModules Λ S) 0 0
        ((DerivedCategory.singleFunctor (supportModules Λ S) 0).obj P) ∧
      DerivedCategory.finiteTorAmplitude (supportModules Λ S)
        ((DerivedCategory.singleFunctor (supportModules Λ S) 0).obj P) := by
  have hdual : IsDualizable P :=
    finiteLocallyProjective_isDualizable _ S P hP
  have hflat : ObjectProperty.flat P := ObjectProperty.flat_of_isDualizable hdual
  have htor := DerivedCategory.torAmplitudeIn_singleFunctor_obj_of_flat hflat
  exact ⟨hflat, htor, ⟨0, 0, htor⟩⟩

end WeilConjectures.CondensedPoincareDualityConventions
