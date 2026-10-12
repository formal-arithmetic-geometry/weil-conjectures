/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U1
-/
module

import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.KrullDimension.Basic
import Sheaf.RingTheory.SmoothNormalRing
import Sheaf.RingTheory.EtaleNormalRing

/-!
# Extending a punctured cover over a smooth trait

Source: Stacks Project, Tags 0EYE and 0EYJ, trait paragraph.
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- A punctured finite etale cover that has an etale model near a point of the
special fibre extends to a finite etale cover. No normality or density assumption
on the given model N is needed for this existence assertion.

Source: Stacks Project, Tags 0EYE and 0EYJ, trait paragraph; Tag 033C for normality.
(blueprint: lem-sbc-trait-etale-extension)

Proof: A Noetherian normal local domain of dimension at most one is either a
field or a DVR. In the field case V is empty; take the empty scheme E, whose
morphism to L is finite etale, whose local rings are vacuously normal, and whose
empty open is dense. The two restrictions to the empty open are isomorphic.
In the DVR case, smoothness implies flatness, so the special fibre is an
effective Cartier divisor. It is regular, since it is smooth over the residue
field. Smoothness and geometric connectedness make this nonempty fibre
integral. Since W contains x on the fibre, W contains its generic point. The
finite etale model n on W shows that the punctured cover is unramified there;
this is the only codimension-one point on that divisor. Away from the divisor
the cover is already etale. Apply Tag 0EYE to obtain a finite etale E over L and
an isomorphism of its restriction with the punctured cover. Smoothness over a
normal base makes L normal; etale ascent then makes all local rings of E normal
(Tag 033C). The puncture is dense in E: a uniformizer is a nonzerodivisor on L
by flatness over the DVR, and remains a nonzerodivisor on E by etale flatness.
Thus its vanishing locus contains no irreducible component of the locally
Noetherian scheme E. Choose the restriction isomorphism in the direction
from N to E; its compatibility with their structure maps gives the equation.
This theorem asserts existence only; no definition selects a witness. -/
theorem exists_finite_etale_extension_of_trait_neighbourhood
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [IsDomain A] [IsIntegrallyClosed A]
    {L N : Scheme.{u}} (q : L ⟶ Spec (.of A))
    [QuasiCompact q] [QuasiSeparated q] [Smooth q] [GeometricallyConnected q]
    (V : (Spec (.of A)).Opens)
    (hV : ∀ t : Spec (.of A), t ∈ V ↔ t ≠ IsLocalRing.closedPoint A)
    (n : N ⟶ L) [IsFinite n]
    (het : Etale (n ∣_ (q ⁻¹ᵁ V)))
    (W : L.Opens) (x : L) (hx : x ∈ W)
    (hqx : q x = IsLocalRing.closedPoint A) (hW : Etale (n ∣_ W))
    (hdim : ringKrullDim A ≤ (1 : WithBot ℕ∞)) :
    ∃ (E : Scheme.{u}) (p : E ⟶ L), IsFinite p ∧ Etale p ∧
      (∀ z : E, IsDomain (E.presheaf.stalk z) ∧
        IsIntegrallyClosed (E.presheaf.stalk z)) ∧
      Dense (↑(p ⁻¹ᵁ (q ⁻¹ᵁ V)) : Set E) ∧
      ∃ e : (n ⁻¹ᵁ (q ⁻¹ᵁ V)).toScheme ≅ (p ⁻¹ᵁ (q ⁻¹ᵁ V)).toScheme,
        e.hom ≫ (p ∣_ (q ⁻¹ᵁ V)) = n ∣_ (q ⁻¹ᵁ V) := by sorry

end AlgebraicGeometry.Scheme
