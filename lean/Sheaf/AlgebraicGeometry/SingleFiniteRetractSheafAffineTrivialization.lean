/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V2
-/
module

public import Sheaf.Paper.DerivedHomMayerVietoris
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.AlgebraicGeometry.AffineScheme
import Sheaf.RingTheory.FiniteProjectiveStandardFreeCover
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde

/-! # Affine trivialization of a single finite free retract

Source: Stacks Project, Tags 00NX, 01IA and 01IB.
(blueprint: new-pc-single-retract-sheaf-affine-trivialization).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- A single retract of a finite free sheaf is finite free near a specified point.

Source: Stacks Project, Tag 00NX (3) implies (7), and Tags 01IA and 01IB.
Proof: Choose an affine neighbourhood W of x inside U. Restriction preserves the
finite free sheaf and the splitting equation. The section followed by retraction
on the ambient free sheaf is an idempotent. Under the affine tilde-Gamma adjunction
it is an idempotent matrix over Gamma(W,O_W). Its image is finite projective, as a
summand of the finite free module. Applying tilde to this module splitting gives
back the restricted sheaf: splittings of the same idempotent are isomorphic.
The finite projective standard free cover supplies a principal open containing x
where the image module is finite free. This open is affine, and localization of
sections and the tilde restriction comparison transport the module basis to a
finite free sheaf isomorphism. Compose restriction comparisons back to U.
Rank zero is allowed; if U is empty no x satisfies hx.
(blueprint: new-pc-single-retract-sheaf-affine-trivialization). -/
theorem exists_affine_trivialization_of_finite_retract
    (X : Scheme.{u}) (U : X.Opens)
    (M : SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
    (hM : ∃ m : ℕ,
      ∃ (ι : M ⟶ SheafOfModules.free
          (R := (moduleRings X.toRingedSpace).over U) (ULift.{u} (Fin m)))
        (π : SheafOfModules.free
          (R := (moduleRings X.toRingedSpace).over U) (ULift.{u} (Fin m)) ⟶ M),
        ι ≫ π = 𝟙 M)
    (x : X) (hx : x ∈ U) :
    ∃ V : X.Opens, x ∈ V ∧ ∃ hVU : V ≤ U, IsAffine V.toScheme ∧
      ∃ r : ℕ, Nonempty
        ((SheafOfModules.overMap (moduleRings X.toRingedSpace) (homOfLE hVU)).obj M ≅
          SheafOfModules.free
            (R := (moduleRings X.toRingedSpace).over V) (ULift.{u} (Fin r))) := by sorry

end AlgebraicGeometry.Scheme
