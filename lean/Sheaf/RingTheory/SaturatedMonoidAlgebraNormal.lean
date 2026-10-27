/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.FineFanBlowup
public import Mathlib.Algebra.MonoidAlgebra.MapDomain
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
import Sheaf.RingTheory.IntegralSupportSaturation

/-!
# Integral closedness of saturated monoid algebras

Source: Illusie--Laszlo--Orgogozo, Exposé VIII, Lemma 3.2.9, printed p. 104
(blueprint: lem-trf-saturated-monoid-algebra-normal).

We use multiplicative notation, as in `AlgebraicGeometry.FineFan.saturation`.
Applying the statement to `Multiplicative G` gives its additive formulation.
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace MonoidAlgebra

/-- A saturated finitely generated submonoid of a torsion-free abelian group, whose
canonical group completion is that ambient group, has monoid algebra integrally closed
in the ambient group algebra. Integrality and membership use the canonical monomial map.

Source: Illusie--Laszlo--Orgogozo, Exposé VIII, Lemma 3.2.9, printed p. 104
(blueprint: lem-trf-saturated-monoid-algebra-normal).

Proof (the agent deduction recorded in the DAG):
1. Write `x` as its finite sum of nonzero monomials. Apply
   `lem-trf-integral-support-saturation` with `P = Q`: finite generation, torsion-freeness
   and integrality imply that every exponent in its support belongs to the saturation of `Q`.
2. The canonical completion hypothesis identifies the ambient group with the completion
   of `Q`. Saturation, in the conventions of `def-trf-fine-fan-blowup`, therefore puts
   every such exponent in `Q` itself.
3. Restrict the finite coefficient function of `x` to `Q`. This gives `y` in `k[Q]`
   whose image under the canonical monomial inclusion is `x`. The map is injective
   because the exponent inclusion is injective. For empty support take `y = 0`.
   Thus every integral element lies in the image of `k[Q]`, as asserted. -/
theorem saturated_monoid_algebra_normal
    (k : Type u) [Field k] (G : Type v) [CommGroup G] [IsMulTorsionFree G]
    (Q : Submonoid G) (hfg : Q.FG)
    (hsat : AlgebraicGeometry.FineFan.saturation Q = Q)
    (hcompletion : Function.Bijective (Algebra.GrothendieckGroup.lift Q.subtype))
    (x : MonoidAlgebra k G)
    (hx : (MonoidAlgebra.mapDomainRingHom k Q.subtype).IsIntegralElem x) :
    ∃ y : MonoidAlgebra k Q, MonoidAlgebra.mapDomainRingHom k Q.subtype y = x := by
  have _ := hcompletion
  have hsupport : ↑x.coeff.support ⊆ Set.range (Q.subtype : Q → G) := by
    intro g hg
    have hgQ : g ∈ Q := by
      rw [← hsat]
      exact support_subset_saturation_of_isIntegral Q hfg x hx g hg
    exact ⟨⟨g, hgQ⟩, rfl⟩
  refine ⟨comapDomain Q.subtype Subtype.val_injective x, ?_⟩
  exact mapDomain_comapDomain hsupport Subtype.val_injective

end MonoidAlgebra
