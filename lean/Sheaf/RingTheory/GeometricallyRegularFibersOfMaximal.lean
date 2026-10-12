/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C3
-/
module

public import Sheaf.RingTheory.GRing
import Sheaf.RingTheory.FibreRingNoetherian
import Sheaf.RingTheory.LocalizationOfRegularRing

/-!
# Geometric regularity of a fibre from maximal target localizations

Source: Stacks Project, More on Algebra, Lemma 07C0, fibre argument.
(blueprint: lem-weil-pbc-geometrically-regular-fiber-of-maximal).
-/

@[expose] public section

universe u v

namespace Algebra

/-- For a fixed source prime, geometric regularity of the fibre can be checked after
localizing the target at each maximal ideal. Flatness is not required.
Source: Stacks Project, More on Algebra, Lemma 07C0, the fibre part of (3) implies (1).
(blueprint: lem-weil-pbc-geometrically-regular-fiber-of-maximal).

Proof: Write F = kappa(p) tensor_R S. It is a localization of S/pS, hence Noetherian.
Fix a finite purely inseparable extension K of kappa(p). The extended fibre F_K is
finite over F, hence Noetherian. Fix a prime n of F_K. Its contraction q to S is a
prime ideal. Choose a maximal ideal m containing q. By hypothesis, the fibre
kappa(p) tensor_R S_m is geometrically regular. Its scalar extension to K is
therefore regular. Tensor product commutes with localization, so this extended
local fibre is the localization of F_K at the images of S minus m. The prime n
avoids these images because its contraction q is contained in m. Thus (F_K)_n is
a localization of the regular extended local fibre and is regular local. The
regular-ring local criterion proves F_K regular. Since K was arbitrary, F is
geometrically regular. For S = 0, all these fibres are zero and regular, so the
vacuous maximal-ideal hypothesis also gives the conclusion. -/
theorem isGeometricallyRegular_fiber_of_localizations_maximal
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing S] (p : Ideal R) [p.IsPrime]
    (h : ∀ (m : Ideal S) [m.IsMaximal],
      IsGeometricallyRegular p.ResidueField (p.Fiber (Localization.AtPrime m))) :
    IsGeometricallyRegular p.ResidueField (p.Fiber S) := by
  sorry

end Algebra
