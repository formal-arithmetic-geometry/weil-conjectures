/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q2
-/
module

public import Sheaf.AlgebraicGeometry.Coherent
public import Sheaf.AlgebraicGeometry.IdealModuleProductStalk
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import Mathlib.AlgebraicGeometry.Noetherian

/-! # HOM ideal-power comparison over an open complement

Source: Stacks Project, Cohomology of Schemes, Lemma 01YB.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- A map that vanishes on the complement vanishes on a sufficiently high ideal-power
submodule. The conclusion is independent of the choice of transition factorization.

Proof: The source I^n G is coherent on a Noetherian scheme. The image Q of χ is
quasi-coherent and finite type on affines (images of finitely many generators suffice),
hence coherent. Its restriction to U is zero, so its support lies in V(I).
The support-power-ideal lemma supplies t with I^t Q = 0. Set m = n+t. On an affine
open W the image of the inclusion of I^m G into G is I(W)^t I(W)^n G(W).
Any factorization r through I^n G is uniquely determined by that inclusion, since the
inclusion of I^n G is mono. By linearity χ sends this submodule into I(W)^t Q(W)=0.
Thus r followed by χ is zero on every affine open, and sheaf separatedness implies
it is zero globally. When U is empty this is the same support-power argument;
when I is the unit ideal the hypothesis already forces χ to vanish.
Source: Stacks Project, Cohomology of Schemes, Lemma 01YB, omitted injectivity,
expanded using Lemma 01Y9 (support-power annihilation).
(blueprint: lem-weil-pbc-coherent-hom-ideal-power-eventually-zero). -/
theorem coherent_hom_ideal_power_eventually_zero {X : Scheme.{u}} [IsLocallyNoetherian X]
    [CompactSpace X] (I : X.IdealSheafData) (F G : X.Modules) [F.IsQuasicoherent]
    (hG : RingedSpace.IsCoherent X.toRingedSpace G) (U : X.Opens)
    (hU : ∀ x : X, x ∈ U ↔ Function.Surjective
      ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).map I.toModulesι).hom)
    (n : ℕ) (χ : idealModuleProduct (idealSheafPower I.toModulesι n).2 G ⟶ F)
    (hχ : (SheafOfModules.overFunctor X.ringCatSheaf U).map χ = 0) :
    ∃ (m : ℕ) (_ : n ≤ m),
      ∀ r : idealModuleProduct (idealSheafPower I.toModulesι m).2 G ⟶
          idealModuleProduct (idealSheafPower I.toModulesι n).2 G,
        r ≫ idealModuleProductι (idealSheafPower I.toModulesι n).2 G =
          idealModuleProductι (idealSheafPower I.toModulesι m).2 G → r ≫ χ = 0 := by sorry

end AlgebraicGeometry.Scheme
