/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.ProperCurveModuli
public import Sheaf.AlgebraicGeometry.OpenModuliSubstack

/-! # Geometric points detect containment of opens in the curve stack -/

@[expose] public noncomputable section

set_option autoImplicit false
universe u v w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry

/-- Containment of full open substacks of proper curves is detected on geometric
objects, including proper algebraic-space curves.
Source: Stacks Project, stacks-properties.tex, Lemma `lemma-open-substacks`;
stacks-morphisms.tex, Tag 0DSN, geometric-point interpretation
(blueprint: lem-sfb-proper-curve-geometric-containment).

Proof: for an object Y of V over a scheme T, use the fibred Yoneda functor of Y
and pull U back to an open immersion W -> T. For each point t of T, take an
algebraic closure of its residue field and pull Y back to that geometric point.
The pullback is a ProperCurveFamily over that field. Stability of V under arrows
puts it in V, and the hypothesis puts it in U. Fullness and the 2-Yoneda comparison
therefore lift the geometric point to W. Thus W -> T is surjective. A surjective
open immersion is an isomorphism, so Y is isomorphic over T to an object in U.
The pullback condition for U along this isomorphism puts Y in U. This proves
containment object by object; the empty base causes no exception. -/
theorem ProperCurveModuli.open_containment_of_geometric_points
    {k : Type u} [Field k]
    (U V : OpenModuliSubstack (ProperCurveModuli.category (Spec (.of k))))
    (h : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
      (a : Spec (.of Ω) ⟶ Spec (.of k)) (X : ProperCurveFamily (Over.mk a)),
      V.property ⟨Over.mk a, X⟩ → U.property ⟨Over.mk a, X⟩) :
    V.IsContainedIn U := by
  sorry

end AlgebraicGeometry
