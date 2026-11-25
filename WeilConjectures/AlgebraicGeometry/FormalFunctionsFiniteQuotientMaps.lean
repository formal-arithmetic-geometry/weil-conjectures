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

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Composing the local germ formula with canonical finite-level pullback gives theta.
(Stacks, Tags 02OD, 01F7, 01FB and 01E4.) -/
theorem formalFunctions_finite_quotient_maps {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsProper f] [IsLocallyNoetherian Y] (F : X.Modules)
    (_hF : RingedSpace.IsCoherent X.toRingedSpace F) (y : Y) (p n : ℕ)
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
  let E₀ := Classical.choice (Scheme.Modules.flatBaseChangeMap_sections_choices
    f (Y.fromSpecStalk y) F I K V)
  let E : Scheme.Modules.FlatBaseChangeOpenChoices f (Y.fromSpecStalk y) F I K V :=
    { E₀ with source := D.source }
  have hfac := formalFunctions_finite_open_factorization f y F p n I K J V E D
  let t := hfac.choose
  have ht := hfac.choose_spec.1
  have htx := hfac.choose_spec.2
  have hl := ha I K V hy E xi
  let rho := Scheme.Modules.moduleCohomologyRestriction
    ((formalFibreι f y n) ⁻¹ᵁ (f ⁻¹ᵁ V))
    ((Scheme.Modules.tensorPullback (formalFibreι f y n)).obj F) p
  refine (congrArg rho (hr _)).trans ?_
  exact (ht _).symm.trans ((congrArg t hl).trans (htx xi))


end
end AlgebraicGeometry
