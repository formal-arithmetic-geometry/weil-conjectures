/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import WeilConjectures.Topology.RingedSpaceModuleCohomology
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import WeilConjectures.AlgebraicGeometry.CohomologyPowersIdealTransitionMaps
import WeilConjectures.AlgebraicGeometry.CohomologyPowersIdealImageBound
import WeilConjectures.AlgebraicGeometry.CohomologyPowersIdealKernelBound

/-! # Image and kernel bounds for cohomology of ideal powers

Forms used (no new definition): `I^n F` is
`Scheme.idealModuleProduct (Scheme.idealSheafPower J.toModulesι n).2 F`, with `J` the extended
ideal sheaf of `I` (hypothesis `hJ`); `H^q(X, -)` as an `A`-module is
`RingedSpace.moduleCohomology` restricted along `(ΓSpecIso A).inv ≫ f.appTop`; the transition
maps `I^k F ⟶ I^n F` are the unique maps over the inclusions into `F`, stated to exist.

## References

* Stacks Project, Tag 02OA
-/

@[expose] public section

universe v

open CategoryTheory

namespace AlgebraicGeometry

/-- Image and kernel bounds for H^q(X, I^n F), with a single uniform constant (Stacks, Tag 02OA). -/
theorem cohomology_powers_ideal_application
    (A : Type v) [CommRing A] [IsNoetherianRing A] {X : Scheme.{v}}
    (I : Ideal A) (f : X ⟶ Spec (CommRingCat.of A)) [IsProper f] (J : X.IdealSheafData)
    (hJ : J = (Scheme.IdealSheafData.ofIdealTop
      (I.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)).comap f)
    (F : X.Modules) (hF : RingedSpace.IsCoherent X.toRingedSpace F) (q : ℕ) :
    ∃ i : ∀ (k n : ℕ), n ≤ k →
        (Scheme.idealModuleProduct (Scheme.idealSheafPower J.toModulesι k).2 F ⟶
          Scheme.idealModuleProduct (Scheme.idealSheafPower J.toModulesι n).2 F),
      (∀ (k n : ℕ) (h : n ≤ k),
        i k n h ≫ Scheme.idealModuleProductι (Scheme.idealSheafPower J.toModulesι n).2 F =
          Scheme.idealModuleProductι (Scheme.idealSheafPower J.toModulesι k).2 F) ∧
      ∃ c : ℕ,
        (∀ (n m : ℕ), c ≤ n + m →
          LinearMap.range ((ModuleCat.restrictScalars
              ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appTop).hom).map
            ((RingedSpace.moduleCohomology X.toRingedSpace q).map
              (i (n + m) n (Nat.le_add_right n m)))).hom ≤
            I ^ (m - (c - n)) • (⊤ : Submodule A ((ModuleCat.restrictScalars
              ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appTop).hom).obj
                ((RingedSpace.moduleCohomology X.toRingedSpace q).obj
                  (Scheme.idealModuleProduct (Scheme.idealSheafPower J.toModulesι n).2 F))))) ∧
        (∀ n : ℕ, c ≤ n →
          LinearMap.ker ((ModuleCat.restrictScalars
              ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appTop).hom).map
            ((RingedSpace.moduleCohomology X.toRingedSpace q).map (i n 0 (Nat.zero_le n)))).hom =
          LinearMap.ker ((ModuleCat.restrictScalars
              ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appTop).hom).map
            ((RingedSpace.moduleCohomology X.toRingedSpace q).map
              (i n (n - c) (Nat.sub_le n c)))).hom) := by
  obtain ⟨i, hi⟩ := cohomology_powers_ideal_transition_maps J F
  obtain ⟨c₁, hc₁⟩ := cohomology_powers_ideal_image_bound A I f J hJ F hF q i hi
  obtain ⟨c₂, hc₂⟩ := cohomology_powers_ideal_kernel_bound A I f J hJ F hF q i hi
  exact ⟨i, hi, max c₁ c₂, hc₁ _ (le_max_left _ _), hc₂ _ (le_max_right _ _)⟩

end AlgebraicGeometry
