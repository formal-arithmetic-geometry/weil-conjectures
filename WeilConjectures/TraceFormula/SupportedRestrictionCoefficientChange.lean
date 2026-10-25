/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.ExchangeRestriction
public import WeilConjectures.TraceFormula.SupportedRestriction

/-!

# The supported restriction under a change of coefficients

The supported restriction `ρ_P : Lι^* Rc^! P ⟶ Rd^! LΔ^* P` of a fixed square
(`ProEtale.CondensedRing.Correspondence.FixedLocus.supportedRestriction`, blueprint
`det-tf-supported-restriction`) is a formal consequence of the adjunctions `c_! ⊣ c^!`,
`d_! ⊣ d^!` and of compact-support base change `σ : c_! ⋙ Δ^* ≅ ι^* ⋙ d_!`: its `d_! ⊣ d^!`
adjoint is `σ⁻¹` followed by `Δ^*` of the counit of `c_! ⊣ c^!`
(`FixedLocus.homEquiv_symm_supportedRestriction`). This file isolates that construction,
`CategoryTheory.Adjunction.exchangeRestriction`, and proves that it commutes with any change of
coefficients `T` which commutes with `c_!`, `d_!`, `ι^*` and `Δ^*` compatibly with base change
(`CategoryTheory.Adjunction.map_exchangeRestriction_comp`): the image under `T` of the supported
restriction, followed by the exchange `T ⋙ Rd^! ⟶ Rd'^! ⋙ T` (the mate of the lower-shriek
comparison), is the exchange for `c^!` followed by the supported restriction for the new
coefficients. This is the coefficient compatibility of `ρ` used to transport the vanishing of the
supported restriction between coefficient rings (blueprint `sk-lem-tf-curve-restriction-zero`,
last step); the inputs are the coefficient comparisons of blueprint `sk-prop-scalar-six` and the
compatibility of base change with them (blueprint `sk-thm-sf-package`, (2)).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Obj


namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

attribute [local instance] boundedConstructibleBraiding

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom]
  [QuasiCompact X.hom] [IsSeparated X.hom] {K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧}
  {c : Correspondence ℓ K}

/-- The supported restriction is the exchange restriction of the fixed square: the adjoint of
compact-support base change followed by `Δ^*` of the counit of `Rc_! ⊣ Rc^!`. -/
lemma Correspondence.FixedLocus.supportedRestriction_eq_exchangeRestriction (F : c.FixedLocus)
    (P : Dᵇc((X ⨯ X).left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    F.supportedRestriction P =
      (boundedConstructibleUpperShriekAdjunction _ ℓ c.support).exchangeRestriction
        (boundedConstructibleUpperShriekAdjunction _ ℓ F.d)
        (boundedConstructibleUpperStar _ ℓ F.ι)
        (boundedConstructibleUpperStar _ ℓ (diag X)) F.lowerShriekBaseChangeIso P := by
  rw [Adjunction.exchangeRestriction, ← F.homEquiv_symm_supportedRestriction]
  exact (Equiv.apply_symm_apply _ _).symm

end AlgebraicGeometry.ProEtale.CondensedRing
