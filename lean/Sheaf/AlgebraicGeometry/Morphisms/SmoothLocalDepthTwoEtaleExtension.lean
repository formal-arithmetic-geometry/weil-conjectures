/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E2
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Fiber
public import Sheaf.RingTheory.Depth

import Sheaf.RingTheory.FlatLocalDepthFormula

/-!
# Extending a finite etale cover across a depth-two local fibre

Source: Stacks Project, Tags 0EYB and 0EY6.
(blueprint: lem-sbc-smooth-local-depth-two-etale-extension)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- A fibrewise dense open containing every nonclosed fibre admits finite etale extension.

Source: Stacks Project, Tag 0EYB, Lemma 58.26.3, and Tag 0EY6, Lemma 58.21.5.
(blueprint: lem-sbc-smooth-local-depth-two-etale-extension)

Proof: Put S = Spec A and a its closed point. For s different from a, the whole
fibre is in U by haway; thus U_s is dense in L_s. The same density at a is hclosed.
If depth O_{S,s} is at most one, then s cannot equal a: the canonical isomorphism
O_{S,a} = A identifies its depth with depth A, which is at least two. Consequently
L_s = U_s at every point of base depth at most one. These are exactly the hypotheses
of 0EYB. Apply its essential surjectivity to f to obtain the finite etale morphism p
and the displayed isomorphism over U. More explicitly, 0337 propagates depth at
least two to every point outside U, and 0EY6 constructs the finite algebra as the
pushforward of f_* O_X. Its formation commutes with flat base change. The proof of
0EYB checks etaleness of this extension after finite flat residue-field extension,
etale localization at a section, and completion to a power series ring; purity for
that power series ring and faithfully flat descent give etaleness on L. This is an
extension theorem for an arbitrary cover of U; it asserts nothing about any given
finite normal cover of L. Empty covers and U = L are included. -/
theorem exists_finite_etale_extension_of_local_depth_two
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {L : Scheme.{u}} (q : L ⟶ Spec (.of A)) [Smooth q]
    (U : L.Opens)
    (haway : ∀ y : L, q y ≠ IsLocalRing.closedPoint A → y ∈ U)
    (hclosed : Dense (↑((q.fiberι (IsLocalRing.closedPoint A)) ⁻¹ᵁ U) :
      Set (q.fiber (IsLocalRing.closedPoint A))))
    (hdepth : (2 : ℕ∞) ≤ IsLocalRing.depth (R := A) A)
    {X : Scheme.{u}} (f : X ⟶ U.toScheme) [IsFinite f] [Etale f] :
    ∃ (E : Scheme.{u}) (p : E ⟶ L), IsFinite p ∧ Etale p ∧
      ∃ e : (p ⁻¹ᵁ U).toScheme ≅ X, e.hom ≫ f = p ∣_ U := by sorry

end AlgebraicGeometry.Scheme
