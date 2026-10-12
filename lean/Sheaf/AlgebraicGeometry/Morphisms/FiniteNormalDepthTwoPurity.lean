/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Sheaf.RingTheory.Depth

import Sheaf.RingTheory.SmoothNormalRing
import Sheaf.RingTheory.EtaleNormalRing
import Sheaf.RingTheory.FlatLocalDepthFormula

/-!
# FiniteNormalDepthTwoPurity

Source: Stacks Project, Tags 0EYB, 0EY6 and 0EYJ (depth-two case).
(blueprint: lem-sbc-finite-normal-depth-two-purity)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- Purity for finite normal covers in the indicated local-base case.

Source: Stacks Project, Tags 0EYB, 0EY6 and 0EYJ (depth-two case).
(blueprint: lem-sbc-finite-normal-depth-two-purity)

Proof: Let T be the union of q inverse V and W. The restrictions of n to both
opens are etale, hence n restricted to T is a finite etale cover. Every fibre away
from the closed point is contained in T. The closed fibre is integral because q is
smooth and geometrically connected; W meets it, so T is dense in it. The local base
has depth at least two, while every other base point has its whole fibre in T.
Tag 0EYB therefore extends this cover to a finite etale cover E of L. The scheme L
is normal by smoothness over a normal base, and E is normal by etaleness. Density
excludes vertical components of N. On each component the finite normal algebras of
N and E are the integral closure of the base algebra in the same generic algebra,
so they agree. This gives an isomorphism over L and proves etaleness of n. The depth
test in 0EYB uses the flat local depth formula of Tag 0337; the extension and its
uniqueness are the depth-two construction of Tag 0EY6. -/
theorem finite_normal_etale_of_depth_two_neighbourhood
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [IsDomain A] [IsIntegrallyClosed A]
    {L N : Scheme.{u}} (q : L ⟶ Spec (.of A))
    [QuasiCompact q] [QuasiSeparated q] [Smooth q] [GeometricallyConnected q]
    (V : (Spec (.of A)).Opens)
    (hV : ∀ t : Spec (.of A), t ∈ V ↔ t ≠ IsLocalRing.closedPoint A)
    (n : N ⟶ L) [IsFinite n]
    (hnormal : ∀ z : N, IsDomain (N.presheaf.stalk z) ∧
      IsIntegrallyClosed (N.presheaf.stalk z))
    (hdense : Dense (↑(n ⁻¹ᵁ (q ⁻¹ᵁ V)) : Set N))
    (het : Etale (n ∣_ (q ⁻¹ᵁ V)))
    (W : L.Opens) (x : L) (hx : x ∈ W)
    (hqx : q x = IsLocalRing.closedPoint A) (hW : Etale (n ∣_ W))
    (hdepth : (2 : ℕ∞) ≤ IsLocalRing.depth (R := A) A) : Etale n := by sorry

end AlgebraicGeometry.Scheme
