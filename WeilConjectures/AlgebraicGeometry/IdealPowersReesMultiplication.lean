/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import WeilConjectures.AlgebraicGeometry.IdealModuleProductStalk
public import WeilConjectures.Blowup.Affine.ReesGrading
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

import WeilConjectures.AlgebraicGeometry.IdealPowersReesMultiplicationComponent

/-!
# Multiplication maps on ideal powers

## References

* Stacks Project, Tag 02O8
-/

@[expose] public section

set_option autoImplicit false
universe v
open CategoryTheory Opposite
namespace AlgebraicGeometry

/-- Multiplication by a homogeneous Rees coefficient lifts to the ideal-power products.
(Stacks, Tag 02O8) -/
theorem idealPowersReesMultiplication {A : Type v} [CommRing A]
    {X : Scheme.{v}} (f : X ⟶ Spec (CommRingCat.of A))
    (I : Ideal A) (J : X.IdealSheafData)
    (hJ : J = (Scheme.IdealSheafData.ofIdealTop
      (I.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)).comap f)
    (F : X.Modules) [F.IsQuasicoherent] :
    let G := fun m ↦ Scheme.idealModuleProduct (Scheme.idealSheafPower J.toModulesι m).2 F
    let graded := reesGrading I
    ∃ mu : ∀ (m k : ℕ), graded k → (G m ⟶ G (m + k)),
      (∀ (m k : ℕ) (b : graded k) (U : X.Opens) (s : (G m).val.obj (op U)),
        ((Scheme.idealModuleProductι (Scheme.idealSheafPower J.toModulesι (m + k)).2 F).app
          U).hom ((mu m k b).app U s) =
        (((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appLE ⊤ U le_top).hom
          (b.val.val.coeff k)) •
        ((Scheme.idealModuleProductι (Scheme.idealSheafPower J.toModulesι m).2 F).app
          U).hom s) := by
  classical
  dsimp
  let G := fun m ↦ Scheme.idealModuleProduct (Scheme.idealSheafPower J.toModulesι m).2 F
  let graded := reesGrading I
  have h := idealPowersReesMultiplication_component f I J hJ F
  choose mu hmu using h
  exact ⟨mu, fun m k b U s => hmu m k b U s⟩

end AlgebraicGeometry
