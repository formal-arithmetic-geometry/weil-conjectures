/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.ClosedSiteLift
public import Mathlib.CategoryTheory.Adjunction.Basic
import WeilConjectures.AlgebraicGeometry.ProEtale.AffineClosedSiteFunctorProperties
import Mathlib.CategoryTheory.Adjunction.FullyFaithful

/-! # Adjunction for the closed-site lift

Source: blueprint, smooth purity, `proposition-extension-zero-restriction-closed-subscheme`, order
1844; Stacks Project, Tags 09BK and 097P (blueprint:
proposition-extension-zero-restriction-closed-subscheme).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.AffineProEt

/-- The closed-site lift is left adjoint to base change, with invertible unit.
Source: blueprint order 1844; Stacks Project, Tags 09BK and 097P
(blueprint: proposition-extension-zero-restriction-closed-subscheme).

Proof plan:
1. For affine objects V = Spec C over A/I and U = Spec D over A, use the
contravariant affine-spectrum Hom correspondence (def-weil-affine-spectrum) and
Algebra.ClosedLift.exists_natural_homEquiv (proposition-extension-zero-restriction-closed-subscheme)
to obtain Hom(v(V), U) ≃ Hom(V, u(U)), naturally in both variables. The over-base triangle
conditions are exactly compatibility with the algebra structures.
2. Reverse the algebra unit and counit by Spec to obtain the site counit and unit.
Their naturality follows by contravariant functoriality; the two algebra triangle
identities become exactly the two site triangle identities.
3. The site unit at V is Spec of the reduction map H_A(C)/IH_A(C) → C, since the
algebra Hom correspondence sends the identity to this reduction. It is invertible
by Algebra.ClosedLift.bijective_reduction (proposition-extension-zero-restriction-closed-subscheme).
The inverses of these components are natural, by composing the unit naturality
squares with the component inverses, so the unit is a natural isomorphism.
Thus the identification of uv with the identity is the adjunction's own unit. -/
theorem exists_closedSiteAdjunction (A : Type u) [CommRing A] (I : Ideal A) :
    ∃ adj : closedSiteLift A I ⊣ closedSiteBaseChange A I, IsIso adj.unit := by
  obtain ⟨_, _, hfull, hfaithful, _, ⟨adj⟩, _, _⟩ :=
    affine_closed_site_functor_properties A I
  have : (closedSiteLift A I).Full := hfull
  have : (closedSiteLift A I).Faithful := hfaithful
  exact ⟨adj, adj.unit_isIso_of_L_fully_faithful⟩

end AlgebraicGeometry.Scheme.AffineProEt
