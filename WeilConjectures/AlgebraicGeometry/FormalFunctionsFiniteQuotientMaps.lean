/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FormalFunctionsFinitePullback
import WeilConjectures.AlgebraicGeometry.FlatBaseChangeOpenChoicesExist
import WeilConjectures.AlgebraicGeometry.SpecLocalRingCanonicalMorphism
import WeilConjectures.AlgebraicGeometry.FormalFunctionsFiniteOpenFactorization

/-! # Finite pullback of the local germ formula

## References

* Stacks Project, Tags 02OD, 01F7, 01FB and 01E4
-/

@[expose] public section

universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite IsLocalRing
namespace AlgebraicGeometry
noncomputable section

-- Compare cohomology h-maps by their interfaces, without unfolding chosen resolutions.
attribute [local irreducible] Scheme.Modules.moduleCohomologyFMap

-- The coherence hypothesis belongs to the existing interface; this compatibility is formal.
set_option linter.unusedVariables false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 400000 in
-- Nested cohomology restrictions and resolution comparisons need extra elaboration heartbeats.
/-- Composing the local germ formula with canonical finite-level pullback gives theta.
(Stacks, Tags 02OD, 01F7, 01FB and 01E4.) -/
theorem formalFunctions_finite_quotient_maps {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsProper f] [IsLocallyNoetherian Y] (F : X.Modules)
    (hF : RingedSpace.IsCoherent X.toRingedSpace F) (y : Y) (p n : ℕ)
    (r : formalFunctionsLocalCohomology f y F p →ₗ[Y.presheaf.stalk y]
      formalFibreCohomologyLocal f y F p n)
    (hr : ∀ z, r z = formalFunctionsFinitePullback f y F p n z)
    (a : formalFunctionsStalk f y F p →ₗ[Y.presheaf.stalk y]
      formalFunctionsLocalCohomology f y F p)
    (ha : IsFormalFunctionsLocalComparison f y F p a) :
    IsFormalFunctionsTheta f y F p n (r.comp a) := by
  classical
  have : Flat (Y.fromSpecStalk y) :=
    (Scheme.fromSpecStalk_local_properties Y y).2.2.2.2.2
  have : Flat (pullback.snd (Y.fromSpecStalk y) f) := inferInstance
  have : EnoughInjectives (pullback (Y.fromSpecStalk y) f).Modules :=
    Scheme.Modules.enoughInjectives (X := _)
  intro I J V hy D xi
  let K := injectiveResolution
    ((Scheme.Modules.tensorPullback (pullback.snd (Y.fromSpecStalk y) f)).obj F)
  obtain ⟨E₀⟩ := Scheme.Modules.flatBaseChangeMap_sections_choices
    f (Y.fromSpecStalk y) F I K V
  let E : Scheme.Modules.FlatBaseChangeOpenChoices f (Y.fromSpecStalk y) F I K V :=
    { E₀ with source := D.source }
  obtain ⟨t, ht, htx⟩ := formalFunctions_finite_open_factorization f y F p n I K J V E D
  have hl := ha I K V hy E xi
  let rho := Scheme.Modules.moduleCohomologyRestriction
    ((formalFibreι f y n) ⁻¹ᵁ (f ⁻¹ᵁ V))
    ((Scheme.Modules.tensorPullback (formalFibreι f y n)).obj F) p
  have hrc (z : formalFunctionsLocalCohomology f y F p) :
      rho (r z) = rho (formalFunctionsFinitePullback f y F p n z) :=
    congrArg rho (hr z)
  let rho' := Scheme.Modules.moduleCohomologyRestriction
    ((pullback.snd (Y.fromSpecStalk y) f) ⁻¹ᵁ (f ⁻¹ᵁ V))
    ((Scheme.Modules.tensorPullback (pullback.snd (Y.fromSpecStalk y) f)).obj F) p
  have hcomb (z : formalFunctionsLocalCohomology f y F p) :
      rho (r z) = t (rho' z) := (hrc z).trans (ht z).symm
  have hright := (congrArg t hl).trans (htx xi)
  have hresult := (hcomb _).trans hright
  simpa only [rho, LinearMap.comp_apply, E, Scheme.Modules.moduleCohomologyRestriction]
    using hresult


end
end AlgebraicGeometry
