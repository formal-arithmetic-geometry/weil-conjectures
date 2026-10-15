/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NF
-/
module

public import Sheaf.AlgebraicGeometry.ProEtale.ClosedSiteLift
public import Mathlib.CategoryTheory.Adjunction.Basic
import Sheaf.RingTheory.ProEtale.ClosedLiftAdjunction
import WeilConjectures.RingTheory.ProEtale.ClosedLift
import Mathlib.AlgebraicGeometry.Scheme

/-! # Adjunction for the closed-site lift

Source: blueprint, smooth purity, `sk-prop-sf-open-closed-triangle`, order 1844;
Stacks Project, Tags 09BK and 097P (blueprint: lem-exc-closed-site-adjunction).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.AffineProEt

/-- The closed-site lift is left adjoint to base change, with invertible unit.
Source: blueprint order 1844; Stacks Project, Tags 09BK and 097P
(blueprint: lem-exc-closed-site-adjunction).

Proof plan:
1. For affine objects V = Spec C over A/I and U = Spec D over A, use the
contravariant affine-spectrum Hom correspondence (def-weil-affine-spectrum) and
Algebra.ClosedLift.exists_natural_homEquiv (lem-exc-closed-lift-adjunction) to obtain
Hom(v(V), U) ≃ Hom(V, u(U)), naturally in both variables. The over-base triangle
conditions are exactly compatibility with the algebra structures.
2. Reverse the algebra unit and counit by Spec to obtain the site counit and unit.
Their naturality follows by contravariant functoriality; the two algebra triangle
identities become exactly the two site triangle identities.
3. The site unit at V is Spec of the reduction map H_A(C)/IH_A(C) → C, since the
algebra Hom correspondence sends the identity to this reduction. It is invertible
by Algebra.ClosedLift.bijective_reduction (lem-exc-closed-lift-reduction).
The inverses of these components are natural, by composing the unit naturality
squares with the component inverses, so the unit is a natural isomorphism.
Thus the identification of uv with the identity is the adjunction's own unit. -/
theorem exists_closedSiteAdjunction (A : Type u) [CommRing A] (I : Ideal A) :
    ∃ adj : closedSiteLift A I ⊣ closedSiteBaseChange A I, IsIso adj.unit := sorry

end AlgebraicGeometry.Scheme.AffineProEt
