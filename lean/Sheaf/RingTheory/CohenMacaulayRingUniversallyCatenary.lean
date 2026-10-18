/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q31
-/
module

public import Sheaf.RingTheory.ExcellentRing
public import Sheaf.RingTheory.Depth
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Noetherian.Defs
import Sheaf.RingTheory.MaximalChainLengthOfDepth
import Sheaf.RingTheory.PolynomialAlgebraCohenMacaulay

/-!
# Noetherian Cohen–Macaulay rings are universally catenary

Source: Stacks Project, Algebra, Tag 00NM, lemma-CM-ring-catenary
(blueprint: lem-trf-cm-ring-universally-catenary).

## Main statement

- `IsUniversallyCatenary.of_local_depth_eq_dimension` states that a
  Noetherian ring whose prime localizations have depth equal to Krull dimension
  is universally catenary.
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace IsUniversallyCatenary

/-- A Noetherian ring whose localizations are Cohen–Macaulay is universally catenary.

Source: Stacks Project, Algebra, Tag 00NM, lemma-CM-ring-catenary
(blueprint: lem-trf-cm-ring-universally-catenary).

The proof follows Tag 00NM. For a polynomial ring over the given ring, use the
polynomial Cohen–Macaulay theorem (Tag 00ND). For comparable primes, finite
local dimension bounds all chains. A longest chain ending at the lower prime is
concatenated with any saturated chain to the upper prime; the maximal-chain
formula for Cohen–Macaulay local rings (Tag 00N9), applied at both endpoints,
forces every such chain to have the same length. A finite-type algebra is a
quotient of a polynomial ring, and the quotient prime correspondence identifies
prime intervals and saturated chains. The resulting catenarity for every
finite-type algebra is exactly universal catenarity.
-/
theorem of_local_depth_eq_dimension {R : Type u} [CommRing R]
    [IsNoetherianRing R]
    (hCM : ∀ (p : Ideal R) [p.IsPrime],
      ((IsLocalRing.depth (R := Localization.AtPrime p)
          (Localization.AtPrime p) : ℕ∞) : WithBot ℕ∞) =
        ringKrullDim (Localization.AtPrime p)) :
    IsUniversallyCatenary R := by
  sorry

end IsUniversallyCatenary
