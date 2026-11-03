/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CompleteDerivedCompletion.CompleteExchangeMap
public import WeilConjectures.AlgebraicGeometry.CompleteDerivedCompletion.CompletePullbackReduction
public import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare

/-!
# Compatibility of ordinary and completed exchange

Source: literature/blueprint/latest/blueprint/part-six-operations/
sec-reduction-finite-coefficients/sec-proper-direct-image/sk-thm-sfb-proper-base-change/
det-pbc-complete-constructible.proof.md, proof (3), the completion-unit naturality square
(blueprint: lem-sfb-complete-exchange-ordinary-compatibility).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.ProEtale.CompleteDerivedCompletion

attribute [local instance] AdicCompletion.ringMonoidalObject AdicCompletion.ringCommutative
  AdicCompletion.modulesDerived AdicCompletion.finiteRingMonoidalObject
  AdicCompletion.finiteRingCommutative AdicCompletion.finiteModulesDerived

/-- The completion units commute with ordinary and completed exchange for a Cartesian
square: `Ex^comp_K ∘ κ_{g^* Rp_* K} = Rp'_* κ_{g'^* K} ∘ Ex_K`. The left completion unit
is `completedPullUnit` (κ followed by lemma-weil-pbc-completed-pullback-reduction (1));
the right one is `κ_{Rp'_* g'^* K}` under prop-weil-pbc-direct-image-limits (1)-(3).

Source: det-pbc-complete-constructible.proof.md, proof (3), in
part-six-operations/sec-reduction-finite-coefficients/sec-proper-direct-image/
sk-thm-sfb-proper-base-change (blueprint: lem-sfb-complete-exchange-ordinary-compatibility).

Proof:
1. For `u = p, p'`, the push comparison `h_u : F_T Ru_* ≅ Ru_*^Tow F_T'`
   (prop-weil-pbc-direct-image-limits (2)) satisfies the counit mate equation with the
   pull comparison `a_u` (lemma-weil-pbc-completed-pullback-reduction (1)), by
   lem-weil-pbc-direct-image-cone-tower-strictness and
   lem-weil-pbc-direct-image-cone-tower-k-injective-normalization.
2. The four `a_u` form a commuting cube with the pullback comparison θ of
   det-pbc-complete-exchange-map (1) and its tower version: on the two cone summands
   `M`, `M[1]` both routes are `θ_M`, `θ_M[1]`; an equality of complexes of towers
   before localization.
3. With `A = g^* Rp_* K`, `B = Rp'_* g'^* K`, `b_A = g^*_Tow h_p ∘ a_g⁻¹` and
   `b_B = Rp'^Tow_* a_{g'}⁻¹ ∘ h_{p'}`, lem-weil-pbc-coefficient-exchange-mates (fed by
   steps 1 and 2) gives `b_B ∘ red(Ex_K) = Ex^Tow_{red K} ∘ b_A` in `D(Tow(Y'))`.
4. Applying `Rlim` and the identifications of lemma-weil-pbc-completed-pullback-reduction
   (1) and prop-weil-pbc-direct-image-limits (1), (2), `Rlim red(Ex_K)` becomes the
   composite defining `Ex^comp_K` (det-pbc-complete-exchange-map (2)).
5. Naturality of κ (det-pbc-complete-derived-completion, notation 4) gives
   `Rlim red(Ex_K) ∘ κ_A = κ_B ∘ Ex_K`; by step 4 and prop-weil-pbc-direct-image-limits (3)
   (`κ_B` corresponds to `Rp'_* κ_{g'^* K}`) this is the asserted equation. Neither
   completeness of `K` nor properness of `p` is used. -/
theorem completeExchange_ordinary_compatibility
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {p' : X' ⟶ Y'}
    {p : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : ChosenCartesianSquare g' p' p g)
    (K : DerivedCategory (AdicCompletion.Modules l E X)) :
    (completedPullUnit l E g).app ((rpushModule l E p).obj K) ≫
        completedExchangeMap l E sq.toCommSq K =
      (moduleExchange l E sq.toCommSq).app K ≫
        (rpushModule l E p').map ((completedPullUnit l E g').app K) := by
  sorry

end AlgebraicGeometry.ProEtale.CompleteDerivedCompletion
