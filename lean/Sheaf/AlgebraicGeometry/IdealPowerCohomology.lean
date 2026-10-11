/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
import Sheaf.AlgebraicGeometry.CoherentFormalModule
import Sheaf.Topology.RingedSpaceModuleCohomology
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian

/-! # The cohomology system of ideal powers

Source: Stacks Project, Cohomology of Schemes, Lemma 02OA, setup of its proof
(blueprint: def-weil-pbc-ideal-power-cohomology-system).

Products, powers, extended ideals and cohomology reuse the recorded declarations:
`I·O_X` is the landed form `(ofIdealTop (I.map (ΓSpecIso _).inv.hom)).comap f`, and the
`A`-module structure is `restrictScalars ((ΓSpecIso _).inv ≫ f.appTop)`.
The level zero is exactly the original module. The inclusion maps are the unique
factorizations through the (monic) inclusions into that module.
-/

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

noncomputable section

/-- The modules J^n F, with J^0 F = F.
Source: Stacks, Lemma 02OA (blueprint: def-weil-pbc-ideal-power-cohomology-system). -/
def idealPowerModule {X : Scheme.{u}} (J : X.IdealSheafData) (F : X.Modules) :
    ℕ → X.Modules
  | 0 => F
  | n + 1 => Scheme.idealModuleProduct (Scheme.idealSheafPower J.toModulesι (n + 1)).2 F

/-- Their canonical inclusions into F.
Source: Stacks, Lemma 02OA (blueprint: def-weil-pbc-ideal-power-cohomology-system). -/
def idealPowerModuleι {X : Scheme.{u}} (J : X.IdealSheafData) (F : X.Modules) :
    (n : ℕ) → idealPowerModule J F n ⟶ F
  | 0 => 𝟙 F
  | n + 1 => Scheme.idealModuleProductι (Scheme.idealSheafPower J.toModulesι (n + 1)).2 F

/-- The inclusions J^n F → F are monomorphisms (the identity, or an image inclusion).
Source: Stacks, Lemma 02OA (blueprint: def-weil-pbc-ideal-power-cohomology-system). -/
instance idealPowerModuleι_mono {X : Scheme.{u}} (J : X.IdealSheafData) (F : X.Modules)
    (n : ℕ) : Mono (idealPowerModuleι J F n) := by
  cases n with
  | zero => exact inferInstanceAs (Mono (𝟙 F))
  | succ n =>
    exact inferInstanceAs (Mono (image.ι _))

/-- For n ≤ k, J^k F lies in J^n F: the inclusion of J^k F into F vanishes modulo J^n F.
Source: Stacks, Lemma 02OA, setup
(blueprint: def-weil-pbc-ideal-power-cohomology-system).
Proof: for n = 0 the cokernel of the identity is zero. For n > 0 and k ≥ n, products of
k sections of J lie in J^n; multiplying by sections of F, the image subsheaf J^k F is
contained in J^n F, so its inclusion into F composed with F → F/J^n F is zero. -/
theorem idealPowerModuleι_comp_cokernel_π {X : Scheme.{u}}
    (J : X.IdealSheafData) (F : X.Modules) {k n : ℕ} (h : n ≤ k) :
    idealPowerModuleι J F k ≫ cokernel.π (idealPowerModuleι J F n) = 0 := by
  sorry

/-- The canonical inclusion J^k F → J^n F for n ≤ k: the lift of the inclusion of J^k F
through the monic inclusion of J^n F into F.
Source: Stacks, Lemma 02OA (blueprint: def-weil-pbc-ideal-power-cohomology-system). -/
def idealPowerModuleInclusion {X : Scheme.{u}} (J : X.IdealSheafData) (F : X.Modules)
    {k n : ℕ} (h : n ≤ k) : idealPowerModule J F k ⟶ idealPowerModule J F n :=
  Abelian.monoLift (idealPowerModuleι J F n) (idealPowerModuleι J F k)
    (idealPowerModuleι_comp_cokernel_π J F h)

/-- The cohomology module H^q(X, I^n F) at level n of the ideal-power system, with
I^n F formed from I·O_X and with A acting through f^♯.
Source: Stacks, Lemma 02OA (blueprint: def-weil-pbc-ideal-power-cohomology-system). -/
def idealPowerCohomology {A : Type u} [CommRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A)) (I : Ideal A) (F : X.Modules) (q n : ℕ) :
    ModuleCat.{u} A :=
  (ModuleCat.restrictScalars ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appTop).hom).obj
    ((RingedSpace.moduleCohomology X.toRingedSpace q).obj
      (idealPowerModule ((Scheme.IdealSheafData.ofIdealTop
        (I.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)).comap f) F n))

/-- The map on cohomology induced by the canonical inclusion of ideal powers.
Source: Stacks, Lemma 02OA (blueprint: def-weil-pbc-ideal-power-cohomology-system). -/
def idealPowerCohomologyMap {A : Type u} [CommRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A)) (I : Ideal A) (F : X.Modules) (q : ℕ)
    {k n : ℕ} (h : n ≤ k) :
    idealPowerCohomology f I F q k ⟶ idealPowerCohomology f I F q n :=
  (ModuleCat.restrictScalars ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appTop).hom).map
    ((RingedSpace.moduleCohomology X.toRingedSpace q).map
      (idealPowerModuleInclusion ((Scheme.IdealSheafData.ofIdealTop
        (I.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)).comap f) F h))

end

end AlgebraicGeometry
