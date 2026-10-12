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

/-! # Simultaneous affine trivialization of finitely many finite free retracts

Source: Stacks Project, Tags 00NX, 01IA and 01IB.
(blueprint: lem-pc-finite-retract-sheaves-affine-trivialization).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- A finite family of retracts of finite free sheaves becomes finite free on one affine
neighbourhood of a specified point.

Source: Stacks Project, Algebra, Tag 00NX (3) implies (7), and Schemes, Tags 01IA
and 01IB; https://stacks.math.columbia.edu/tag/00NX.
Proof: Choose an affine neighbourhood W of x inside U. Restriction preserves finite
free sheaves and the splitting equations. For each index in s, the composite of its
retraction and section is an idempotent endomorphism of a finite free sheaf on W.
Use the equivalence between the localized-site sheaves on W and W.Modules. The affine
tilde-Gamma adjunction identifies this endomorphism with an idempotent matrix over
Gamma(W,O_W). Its image is a finite projective module, being a summand of a finite
free module. Applying tilde to its splitting yields the original restricted sheaf:
both are splittings of the same idempotent, hence canonically isomorphic.
The finite projective standard free cover supplies, for each of the finitely many
indices, a principal open containing x on which that module is finite free.
Their intersection is again a principal open in W (the product of the elements),
so is affine and contains x. Sections/localization and tilde identify the sheaf
restrictions there with free sheaves of the respective finite ranks. Compose the
nested-restriction comparisons to obtain the stated trivializations. For s empty
use W itself. A zero summand has rank zero; no positive rank is required. If U
is empty there is no x satisfying hx, so no existence claim is imposed.
(blueprint: lem-pc-finite-retract-sheaves-affine-trivialization). -/
theorem exists_affine_trivialization_of_finite_retracts
    (X : Scheme.{u}) (U : X.Opens) (s : Finset ℤ)
    (M : ℤ → SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
    (hM : ∀ n ∈ s, ∃ m : ℕ,
      ∃ (ι : M n ⟶ SheafOfModules.free
          (R := (moduleRings X.toRingedSpace).over U) (ULift.{u} (Fin m)))
        (π : SheafOfModules.free
          (R := (moduleRings X.toRingedSpace).over U) (ULift.{u} (Fin m)) ⟶ M n),
        ι ≫ π = 𝟙 (M n))
    (x : X) (hx : x ∈ U) :
    ∃ V : X.Opens, x ∈ V ∧ ∃ hVU : V ≤ U, IsAffine V.toScheme ∧
      ∀ n ∈ s, ∃ r : ℕ, Nonempty
        ((SheafOfModules.overMap (moduleRings X.toRingedSpace) (homOfLE hVU)).obj (M n) ≅
          SheafOfModules.free
            (R := (moduleRings X.toRingedSpace).over V) (ULift.{u} (Fin r))) := by sorry

end AlgebraicGeometry.Scheme
