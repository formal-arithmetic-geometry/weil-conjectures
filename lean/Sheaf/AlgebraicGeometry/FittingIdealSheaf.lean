/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q108
-/
module

public import Sheaf.RingTheory.PresentationFittingIdeal
public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import Mathlib.AlgebraicGeometry.Scheme
public import WeilConjectures.AlgebraicGeometry.Coherent

/-!
# Fitting ideal sheaves

Source: Stacks Project, Divisors, Section 31.9, Tag 0C3C; More on Algebra,
Tags 07Z8 and 07ZA(3) (blueprint: def-trf-fitting-ideal-sheaf).
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- The Fitting ideal sheaf, constructed without choosing a presentation. On each affine
open take the supremum of the kernel-minor ideals of all finite free surjections onto the
module of sections, and apply `IdealSheafData.ofIdeals` to this family. For a finite-type
quasi-coherent module, finite generation supplies a surjection on every affine open;
presentation independence makes the supremum equal to each presentation ideal, and
localization compatibility makes `ofIdeals` retain this affine family. These properties
are stated in `fitting_ideal_generate_locally`.
Source: Stacks Project, Divisors, Tag 0C3C; More on Algebra, Tags 07Z8 and 07ZA(3).
(blueprint: def-trf-fitting-ideal-sheaf) -/
noncomputable def fittingIdealSheaf {X : Scheme.{u}} (F : X.Modules)
    [F.IsFiniteType] [F.IsQuasicoherent] (r : ℕ) : X.IdealSheafData :=
  IdealSheafData.ofIdeals fun U ↦
    ⨆ (n : ℕ) (π : (Fin n → Γ(X, U.1)) →ₗ[Γ(X, U.1)] Γ(F, U.1))
      (_hπ : Function.Surjective π), π.presentationFittingIdeal r

end AlgebraicGeometry.Scheme.Modules
