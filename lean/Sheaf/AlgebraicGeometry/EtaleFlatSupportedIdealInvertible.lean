/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V1
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Invertible
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.RingTheory.Flat.Basic

/-! # An ideal flat over an etale base and trivial away from a Cartier divisor

Source: Stacks Project, More on Morphisms, Tag 080Q; Divisors, Tag 080F.
(blueprint: lem-per-etale-flat-supported-ideal-invertible).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory

namespace AlgebraicGeometry.Scheme.IdealSheafData

/-- A finitely presented ideal on an etale scheme, flat over the base and equal to the
unit ideal off a base Cartier divisor, is an invertible ideal.

Source: Stacks Project, More on Morphisms, Tag 080Q, combined with Morphisms, Tag 02GL (2),
and Divisors, Tag 080F, the regular Cartier-equation argument.
(blueprint: lem-per-etale-flat-supported-ideal-invertible).

Proof: For a point x over s, the etale fibre has field local ring at x. Its module stalk
is therefore flat. The relative flatness hypothesis and the finite presentation of the
morphism and ideal permit the flat-fibre free-neighbourhood criterion (080Q). Obtain
finite free neighbourhoods for the ideal everywhere. Shrink such a neighbourhood to an
affine Cartier chart: the pulled-back boundary has regular local equation d since the
etale morphism is flat. If the chart ring A is nonzero, A → A_d is injective and A_d is
nonzero. The ideal is the unit ideal on D(d). A local trivialization of rank r therefore
gives A_d^r ≅ A_d; taking a residue field of A_d forces r = 1. Its free generator maps
to a ∈ A, with ideal (a). The inclusion of the ideal is injective, so ca = 0 implies
c = 0: a is regular. These affine neighbourhoods prove IsInvertible. There are no points
to check on the empty scheme. This argument needs neither Noetherianity nor excellence;
finite presentation is used to spread the free stalk to a neighbourhood. -/
theorem isInvertible_of_etale_flat_finitePresentation
    {X S : Scheme.{u}} (f : X ⟶ S) [Etale f] [QuasiCompact f] [IsSeparated f]
    (D : S.IdealSheafData) (hD : D.IsInvertible)
    (K : X.IdealSheafData) [K.toModules.IsFinitePresentation]
    (hflat : ∀ x : X, Module.Flat (S.presheaf.stalk (f x))
      ((ModuleCat.restrictScalars (f.stalkMap x).hom).obj
        ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj K.toModules)))
    (hunit : K.comap (f ⁻¹ᵁ D.support.compl).ι = ⊤) : K.IsInvertible := by sorry

end AlgebraicGeometry.Scheme.IdealSheafData
