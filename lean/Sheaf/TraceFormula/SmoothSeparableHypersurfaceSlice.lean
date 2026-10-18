/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.ResidueField
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.EffectiveCartier
public import WeilConjectures.Mathlib.Topology.KrullDimension

/-!
# Smooth separable hypersurface slice

Source: literature/stacks-project/more-morphisms.tex, Tags 057F and 057C
(blueprint: lem-trf-smooth-separable-hypersurface-slice).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

namespace AlgebraicGeometry

/--
Let `f : X ⟶ S` be smooth and let `x` be a closed point of its fibre whose
residue field is finite separable over the residue field of `f x`.  If the
fibre has positive local dimension `d`, there is an affine neighbourhood and
a Cartier hypersurface through `x` which is smooth over `S` and has local
fibre dimension `d - 1`.

The proof follows Stacks Tags 057F, 057C, and 057G.  First choose affine
smooth charts and identify the fibre local ring and its residue field.  Base
change and localization of Kähler differentials identify the fibre cotangent
space with a nonzero `d`-dimensional vector space.  The Jacobi--Zariski exact
sequence and vanishing of differentials for finite separable extensions then
provide a local equation with nonzero relative differential.  Smoothness over
the residue field gives a regular local domain, so this equation is a
nonzerodivisor.  After extending the local equation to an affine open, the
finite-annihilator argument makes the fibre cut Cartier near the point.  The
fibre-Cartier criterion supplies an ambient Cartier neighbourhood, while the
nonzero-differential hypersurface criterion supplies smoothness after shrinking.
Finally, the quotient dimension formula for a nonzerodivisor and the finite-type
dimension formula give the dimension drop, and the closed immersion gives the
unique point over `x`.
(blueprint: lem-trf-smooth-separable-hypersurface-slice).
-/
theorem exists_affine_smooth_effectiveCartier_hypersurface_slice
    {X S : Scheme.{u}} (f : X ⟶ S) [Smooth f] (x : X)
    (hx : IsClosed {f.asFiber x})
    (hfinite : @FiniteDimensional (S.residueField (f x)) (X.residueField x) _ _
      (f.residueFieldMap x).hom.toAlgebra.toModule)
    (hseparable : @Algebra.IsSeparable (S.residueField (f x)) (X.residueField x) _ _
      (f.residueFieldMap x).hom.toAlgebra)
    (d : ℕ) (hd : 1 ≤ d)
    (hdim : topologicalKrullDimAt (f.asFiber x) = (d : WithBot ℕ∞)) :
    ∃ (U D : Scheme.{u}) (j : U ⟶ X) (i : D ⟶ U) (u : U) (xD : D),
      IsAffine U ∧ IsOpenImmersion j ∧ j u = x ∧
      IsEffectiveCartierCenter i ∧ i xD = u ∧
      Smooth (i ≫ j ≫ f) ∧
      topologicalKrullDimAt ((i ≫ j ≫ f).asFiber xD) =
        ((d - 1 : ℕ) : WithBot ℕ∞) := by
  sorry

end AlgebraicGeometry
