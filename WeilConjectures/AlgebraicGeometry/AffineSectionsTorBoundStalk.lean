/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectMorphism
public import Mathlib.AlgebraicGeometry.AffineScheme
import WeilConjectures.RingTheory.TorVanishingLocalizedAlgebra
import WeilConjectures.RingTheory.TorVanishingLocalizedBase

/-! # Localization of an affine coordinate Tor bound

## References

* Stacks Project, Tags 0B67 and 069C
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A fixed affine coordinate Tor bound holds at every source stalk in that affine open
(Stacks, Tags 0B67 and 069C). -/
theorem affineSections_torBound_stalk
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (U : Y.Opens) (hU : IsAffineOpen U)
    (V : X.Opens) (hV : IsAffineOpen V) (e : V ≤ f ⁻¹ᵁ U)
    (d : ℕ)
    (hbound : ∀ M : ModuleCat.{u} Γ(Y, U), ∀ j : ℕ, d < j →
      IsZero (((Tor' (ModuleCat.{u} Γ(Y, U)) j).obj
        ((ModuleCat.restrictScalars (f.appLE U V e).hom).obj
          (ModuleCat.of Γ(X, V) Γ(X, V)))).obj M)) :
    ∀ y : X, y ∈ V → ∀ M : ModuleCat.{u} (Y.presheaf.stalk (f y)),
      ∀ j : ℕ, d < j →
        IsZero (((Tor' (ModuleCat.{u} (Y.presheaf.stalk (f y))) j).obj
          ((ModuleCat.restrictScalars (f.stalkMap y).hom).obj
            (ModuleCat.of (X.presheaf.stalk y) (X.presheaf.stalk y)))).obj M) := by
  intro y hy M j hj
  let := Y.presheaf.algebra_section_stalk ⟨f y, e hy⟩
  have := hU.isLocalization_stalk ⟨f y, e hy⟩
  let := X.presheaf.algebra_section_stalk ⟨y, hy⟩
  have := hV.isLocalization_stalk ⟨y, hy⟩
  let a := algebraMap Γ(Y, U) (Y.presheaf.stalk (f y))
  let b := algebraMap Γ(X, V) (X.presheaf.stalk y)
  have hcomp : b.comp (f.appLE U V e).hom = (f.stalkMap y).hom.comp a := by
    ext r
    change X.presheaf.germ V y hy ((f.appLE U V e).hom r) =
      f.stalkMap y (Y.presheaf.germ U (f y) (e hy) r)
    simp only [Scheme.Hom.germ_stalkMap_apply, Scheme.Hom.appLE,
      homOfLE_leOfHom, CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply,
      X.presheaf.germ_res_apply]
  have hlocalized := ModuleCat.isZero_tor_localized_algebra
    Γ(Y, U) Γ(X, V) (X.presheaf.stalk y) (f.appLE U V e).hom
    (hV.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl
    ((ModuleCat.restrictScalars a).obj M) j
    (hbound ((ModuleCat.restrictScalars a).obj M) j hj)
  change IsZero (((Tor' (ModuleCat.{u} Γ(Y, U)) j).obj
    ((ModuleCat.restrictScalars (b.comp (f.appLE U V e).hom)).obj
      (ModuleCat.of (X.presheaf.stalk y) (X.presheaf.stalk y)))).obj
        ((ModuleCat.restrictScalars a).obj M)) at hlocalized
  rw [hcomp] at hlocalized
  let c := ModuleCat.restrictScalarsComp'App a (f.stalkMap y).hom
    ((f.stalkMap y).hom.comp a) rfl
    (ModuleCat.of (X.presheaf.stalk y) (X.presheaf.stalk y))
  have hrestricted := hlocalized.of_iso
    (((Tor' (ModuleCat.{u} Γ(Y, U)) j).mapIso c).app ((ModuleCat.restrictScalars a).obj M))
  exact ModuleCat.isZero_tor_of_restrictScalars_localization
    Γ(Y, U) (Y.presheaf.stalk (f y))
    (hU.primeIdealOf ⟨f y, e hy⟩).asIdeal.primeCompl
    ((ModuleCat.restrictScalars (f.stalkMap y).hom).obj
      (ModuleCat.of (X.presheaf.stalk y) (X.presheaf.stalk y))) M j hrestricted

end AlgebraicGeometry
