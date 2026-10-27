/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.ProperCurveModuli

/-! # Proper schemes as objects of the curve stack -/

@[expose] public noncomputable section

set_option autoImplicit false
universe u v w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry

/-- A proper scheme of dimension at most one represents an object of the stack
of proper algebraic-space curves. The comparison is over the given field.
Source: Stacks Project, moduli-curves.tex, definition of the stack in Tag 0DSQ;
moduli-curves.tex, Tag 0DSW(3)(a)
(blueprint: lem-sfb-proper-curve-scheme-realization).

Proof: use the representable fppf sheaf of C over Spec k as the algebraic space,
and use yoneda of f as its projection. Schemes give algebraic spaces by the
representable diagonal and the identity etale atlas. The morphism to Spec Omega
is flat because Omega is a field. Properness gives separatedness, quasi-compactness,
local finite type and universal closedness. A finite-type morphism to a field is
locally of finite presentation; separatedness gives the quasi-compact diagonal.
These properties pass to etale test charts and arbitrary base changes. Every
geometric fibre is the field-extension base change of C, whose dimension agrees
with that of C for a finite-type scheme over a field. These are exactly the fields
of `isCurve`. The underlying presheaf comparison is the identity, so its composite
with yoneda of f is the chosen projection. The construction includes C empty. -/
theorem ProperCurveModuli.exists_scheme_family {k Ω : Type u} [Field k] [Field Ω]
    (a : Spec (.of Ω) ⟶ Spec (.of k)) (C : Scheme.{u})
    (f : C ⟶ Spec (.of Ω)) (hf : IsProper f) (hdim : topologicalKrullDim C ≤ 1) :
    ∃ X : ProperCurveFamily (Over.mk a),
      ∃ e : X.space.obj.obj ≅ yoneda.obj (Over.mk (f ≫ a)),
        e.hom ≫ yoneda.map
          (Over.homMk (U := Over.mk (f ≫ a)) (V := Over.mk a) f rfl) = X.projection := by
  sorry

end AlgebraicGeometry
