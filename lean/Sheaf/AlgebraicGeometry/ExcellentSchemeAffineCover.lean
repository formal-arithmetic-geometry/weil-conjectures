/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.RingTheory.ExcellentRing
public import Mathlib.AlgebraicGeometry.AffineScheme
import Sheaf.AlgebraicGeometry.GRingAffineCover
import Sheaf.AlgebraicGeometry.JTwoAffineCover
import Sheaf.AlgebraicGeometry.UniversallyCatenaryAffineCover
import WeilConjectures.RingTheory.GRing

/-! # Excellence detected on affine open covers

Source: Stacks Project, Morphisms, Tag 0HAB (blueprint: lem-trf-excellent-scheme-affine-cover).
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open scoped AlgebraicGeometry

namespace AlgebraicGeometry

universe u v

set_option autoImplicit false

/-- Excellence of affine coordinate rings descends from an affine open cover.

Source: Stacks Project, Morphisms, Tag 0HAB, implication (3) implies (2) and final
assertion (blueprint: lem-trf-excellent-scheme-affine-cover).

The proof first obtains local Noetherianity from the excellent chart rings. It then applies
locality of the G-ring, J-2, and universally catenary conditions on affine opens, and
recombines these conditions with the definition of excellence. For an open subscheme,
the affine-open basis supplies a cover and restriction identifies its section rings with
those on the ambient scheme. -/
theorem isExcellent_of_affine_open_cover
    {X : Scheme.{u}} {I : Type v} (U : I → X.Opens)
    (hcover : TopologicalSpace.IsOpenCover U)
    (haff : ∀ i : I, IsAffineOpen (U i))
    (hexc : ∀ i : I, IsExcellent Γ(X, U i)) :
    (∀ V : X.Opens, IsAffineOpen V → IsExcellent Γ(X, V)) ∧
      (∀ W : X.Opens,
        ∀ V : (W.toScheme).affineOpens, IsExcellent Γ(W.toScheme, V)) := by
  sorry

end AlgebraicGeometry
