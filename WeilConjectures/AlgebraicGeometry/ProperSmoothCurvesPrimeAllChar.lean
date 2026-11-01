/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.Topology.KrullDimension
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
import WeilConjectures.AlgebraicGeometry.Proper.Smooth.ProperSmoothCurvesPrimeCoefficients

/-!
# Prime coefficients in proper smooth curve families in every characteristic

This is the prime-coefficient part of Stacks Project, Tag 0GKW.  It is separated
from the finite-module dévissage so that the characteristic-p argument is explicit.
(blueprint: lem-fd-proper-smooth-curves-prime-all-char)
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

/-- Prime coefficients for proper smooth geometrically connected relative curves.

Source: Stacks Project, more-etale.tex, Tags 0GKV and 0GKW.
(blueprint: lem-fd-proper-smooth-curves-prime-all-char)

Proof: use the clopen dimension-zero/dimension-one decomposition.  On the
dimension-zero locus, proper plus quasi-finite is finite and finite direct image
is exact.  On the dimension-one locus split the base into the open where `p` is
invertible and the closed characteristic-`p` locus.  The open part is the
prime-coefficient theorem `properSmoothCurves_prime_higherDirectImage_constructible`.
On the closed part, proper base change, Artin--Schreier, and the Frobenius-fixed
sections sequence reduce the assertion to the kernel of Frobenius minus identity
on the finite locally free degree-one structure-cohomology bundle.  The
Frobenius-linear vector-bundle constructibility theorem, finite geometric stalks,
and the module/abelian comparison finish that branch.  The two restrictions are
identified by exact pullback and proper base change, and the finite stratifications
are glued.
-/
theorem properSmoothCurves_prime_higherDirectImage_constructible_all_char
    {C S : Scheme.{u}} [IsLocallyNoetherian S] [CompactSpace S]
    (f : C ⟶ S) [IsProper f] [Smooth f] [GeometricallyConnected f]
    (h_dim : ∀ s : S, topologicalKrullDim (f.fiber s) ≤ 1)
    (p : ℕ) [Fact p.Prime] (q : ℤ) :
    Scheme.IsConstructibleEtaleModuleSheaf
      ((DerivedCategory.Plus.homologyFunctor
        (Sheaf S.smallEtaleTopology
          (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod p)))) q).obj
        ((rightDerivedLowerStarPlus
          (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod p))) f).obj
          ((DerivedCategory.Plus.singleFunctor
            (Sheaf C.smallEtaleTopology
              (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod p)))) 0).obj
            ((constantSheaf C.smallEtaleTopology
              (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod p)))).obj
              (ModuleCat.of (ULift.{u + 1} (ZMod p))
                (ULift.{u + 1} (ZMod p))))))) := by
  sorry

end AlgebraicGeometry.Etale
