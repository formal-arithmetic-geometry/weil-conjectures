/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q43
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism

import Mathlib.AlgebraicGeometry.AffineScheme
import Sheaf.AlgebraicGeometry.IsLocallyQuasiFiniteAffineCriterion
import Sheaf.RingTheory.QuasiFiniteComposition

/-!
# Composition of locally quasi-finite scheme morphisms

Source: Stacks Project, Morphisms of Schemes, Tag 01TL, locally quasi-finite assertion
(blueprint: lem-a1-scheme-lqf-composition).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Hom

/-- The composite of two locally quasi-finite scheme morphisms in the Stacks sense
is locally quasi-finite, including the finite-type affine neighbourhood condition.
Source: Stacks Project, Morphisms of Schemes, Tag 01TL, locally quasi-finite assertion
(blueprint: lem-a1-scheme-lqf-composition).

Proof:
1. Fix `x : X`. By `lem-weil-pbc-affine-opens-basis`, choose an affine open `W`
   of `S` containing `h (f x)`, an affine open `V` of `Y` containing `f x` inside
   the inverse image of `W`, and an affine open `U` of `X` containing `x` inside
   the inverse image of `V`. Thus `f(U)` lies in `V` and `h(V)` lies in `W`.
   This only uses inverse images of opens and the affine basis.
2. Apply the implication (1) to (2) of `lem-a1-scheme-lqf-affine-criterion` to
   `h` on `V,W` and to `f` on `U,V`. The induced maps on sections are of finite
   type and quasi-finite at every prime of their targets. In particular, the
   finite-type conditions required by `pqf-def-quasifinite` have been retained.
3. Apply `lem-trf-quasi-finite-composition` to the maps from sections on `W` to
   sections on `V` and then to sections on `U`. Their composite is of finite type
   and quasi-finite at every target prime. By composition of scheme morphisms,
   this is the section map of `f ≫ h`: a section `a` is sent to `f♯(h♯(a))`.
4. Apply this at the prime of `U` corresponding to `x`. The affine opens `U,W`
   witness `IsQuasiFiniteAtPoint (f ≫ h) x` by `pqf-def-quasifinite`. Since `x`
   was arbitrary, the composite is locally quasi-finite. For empty `X`, this
   universal assertion is vacuous.

No quasi-compactness, separatedness, or Noetherian hypothesis is required. -/
theorem isLocallyQuasiFinite_comp {X Y S : Scheme.{u}} (f : X ⟶ Y) (h : Y ⟶ S)
    (hf : f.IsLocallyQuasiFinite) (hh : h.IsLocallyQuasiFinite) :
    (f ≫ h).IsLocallyQuasiFinite := by
  sorry

end AlgebraicGeometry.Scheme.Hom
