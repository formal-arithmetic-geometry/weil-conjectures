/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q137
-/
module

public import Sheaf.AlgebraicGeometry.ProperCurveVersality
import Sheaf.AlgebraicGeometry.AffineClosedPinchingPushout

/-! # Openness of versality for proper algebraic-space curves

Source: Stacks Project, quot.tex, Tag 0D59 (lemma-curves-defo-thy), over Spec Z;
artin.tex, definition-openness-versality (blueprint: lem-sfb-curve-openness-versality).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.ProperCurveFamily

/-- A proper curve family versal at a finite type point is versal at all finite type
points in an open neighbourhood. A finite type point is one whose canonical residue
field morphism is locally of finite type: its source has a single point, so that
morphism is automatically quasi-compact, giving precisely Stacks' finite type condition.
Versality of `x` at a point of an open equals versality of its restriction, because all
Artinian local test schemes have that one topological point.
Source: Stacks Project, quot.tex, Tag 0D59; artin.tex, definition-openness-versality;
morphisms.tex, definition-finite-type-point
(blueprint: lem-sfb-curve-openness-versality).

Proof:
1. Apply the strong-effectivity criterion to the proper-curve groupoid. The statement
   lem-sfb-curve-descent-isom-spaces supplies descent and representable Isom spaces.
   The affine pushout in lem-sfb-affine-closed-pinching-pushout identifies the relevant
   ring fibre product with the scheme pushout, so lem-sfb-curve-infinitesimal-pushout
   gives (RS*), retaining gluing isomorphisms. Lem-sfb-curve-limit-preservation supplies
   descent of objects and arrows and eventual equality of arrows.
2. For the criterion's inverse system, forget the fibre dimension bound and apply
   lem-sfb-proper-space-square-zero-effectivity to obtain a flat proper finitely
   presented algebraic space over the inverse limit, with compatible reductions.
3. The limit ring surjects onto its first stage by successive lifting. Its kernel is
   square-zero because every transition to that first stage has square-zero kernel.
   Every map to an algebraically closed field kills this kernel, so every geometric
   fibre is a geometric fibre of the first-stage curve. This proves dimension at most
   one, including empty fibres, and the effective object is a proper curve family.
4. Apply lem-sfb-artin-square-zero-effectivity-openness over Spec Z. Its Artinian
   lifting condition extends the given reduction isomorphism, exactly as IsVersalAt
   requires, and its conclusion is the asserted open neighbourhood. -/
theorem exists_open_isVersalAt
    (T : Over (Spec (.of (ULift.{u} ℤ)))) [LocallyOfFiniteType T.hom]
    (x : ProperCurveFamily T) (u₀ : T.left)
    (hft : LocallyOfFiniteType (T.left.fromSpecResidueField u₀))
    (hx : x.IsVersalAt u₀) :
    ∃ V : T.left.Opens, u₀ ∈ V ∧
      ∀ u₁ : T.left, u₁ ∈ V →
        LocallyOfFiniteType (T.left.fromSpecResidueField u₁) → x.IsVersalAt u₁ := by
  sorry

end AlgebraicGeometry.ProperCurveFamily
