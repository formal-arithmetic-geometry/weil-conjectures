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
public import Mathlib.RingTheory.KrullDimension.Basic

import Sheaf.RingTheory.SmoothNormalRing
import Sheaf.RingTheory.EtaleNormalRing

/-!
# FiniteNormalTraitPurity

Source: Stacks Project, Tags 0EYE and 0EYJ (trait case).
(blueprint: lem-sbc-finite-normal-trait-purity)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- Purity for finite normal covers in the indicated local-base case.

Source: Stacks Project, Tags 0EYE and 0EYJ (trait case).
(blueprint: lem-sbc-finite-normal-trait-purity)

Proof: If A has dimension zero it is a field. Then its punctured spectrum is empty,
so density forces N to be empty, and the morphism is etale. Otherwise A is a DVR
because it is a normal Noetherian local domain of dimension at most one. The closed
fibre of q is a regular effective Cartier divisor. Smoothness and geometric
connectedness make this fibre integral, so the nonempty open W meets its generic
point. The cover on the complement is therefore unramified at every codimension-one
point of the divisor. Tag 0EYE extends it to a finite etale cover E of L. Both E and
N are normal. Density excludes components of N supported on the closed fibre;
componentwise, a finite normal algebra is the integral closure of the base in its
generic algebra. Thus N and E are isomorphic over L, and n is etale. -/
theorem finite_normal_etale_of_trait_neighbourhood
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
    (hdim : ringKrullDim A ≤ (1 : WithBot ℕ∞)) : Etale n := by sorry

end AlgebraicGeometry.Scheme
