/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Monoidal.Closed.Basic

/-!
# Evaluation-normalized comparison of inverse pairing adjoints

Source: blueprint main-20261015, `thm-pod-finite-reduction.proof.md`, final paragraph:
taking adjoints in the commuting pairing square and then inverses of the horizontal adjoints.
(blueprint: lem-sf-perfect-pairing-reduction-adjoints)
-/

@[expose] public section

universe u₁ v₁ u₂ v₂

namespace CategoryTheory

open MonoidalCategory

variable {𝒞 : Type u₁} {𝒟 : Type u₂}
  [Category.{v₁} 𝒞] [Category.{v₂} 𝒟]
  [MonoidalCategory 𝒞] [MonoidalCategory 𝒟]
  [MonoidalClosed 𝒞] [MonoidalClosed 𝒟]

/-- The specified comparison `ell = (c⁻¹)ᵛ ∘ h`. The internal-Hom functor maps
`c.symm.op`, so the forward map precomposes with `c.inv`, not with `c.hom`.
Source: blueprint main-20261015, `thm-pod-finite-reduction.proof.md`, final paragraph.
(blueprint: lem-sf-perfect-pairing-reduction-adjoints) -/
def perfectPairingDualComparison (F : 𝒞 ⥤ 𝒟) {C : 𝒞} {C' : 𝒟}
    (c : F.obj C ≅ C')
    (h : F.obj ((ihom C).obj (𝟙_ 𝒞)) ≅ (ihom (F.obj C)).obj (𝟙_ 𝒟)) :
    F.obj ((ihom C).obj (𝟙_ 𝒞)) ≅ (ihom C').obj (𝟙_ 𝒟) :=
  h ≪≫ ((MonoidalClosed.internalHom (C := 𝒟)).mapIso c.symm.op).app (𝟙_ 𝒟)

/-- Evaluation-normalized comparison of perfect pairing adjoints, without assuming
that the second-variable comparison `r` is invertible. The isomorphisms `b`, `b'`
are identified with the actual tensor-Hom transposes by `hb`, `hb'`.
Source: blueprint main-20261015, `thm-pod-finite-reduction.proof.md`, final paragraph.
(blueprint: lem-sf-perfect-pairing-reduction-adjoints)

Proof plan:
1. Apply `lem-pod-closed-uncurry-laws` in both categories to express each pairing
   as evaluation after tensoring its adjoint, and to cancel uncurrying.
2. The same laws characterize precomposition by its evaluation equation.
   Tensor functoriality (`def-sfb-monoidal-category`) gives its identity and composite
   laws, hence dualizing `c.inv` gives an isomorphism with inverse the dual of `c.hom`.
3. Tensor functoriality and the evaluation normalization of `h` give the displayed
   evaluation normalization of `perfectPairingDualComparison F c h`.
4. Evaluate the two candidate maps from `F D` to the dual of `C'`, after tensoring
   with `c`. The pairing square identifies the first with the transported pairing.
   Tensorator naturality (`def-sfb-strong-monoidal-functor`), applied to the identity
   and `b.hom`, identifies the second with that same transported pairing.
5. Cancel the isomorphism `c` tensored with the identity, then use injectivity of
   uncurrying (`lem-pod-closed-uncurry-laws`) to obtain the adjoint square.
6. Functoriality and the inverse identities of `b`, `b'` give the inverse-adjoint
   square and the formula for `r`. The displayed candidate inverse composes with
   `r` to the identity in both orders, giving the asserted isomorphism.
-/
theorem perfectPairing_reduction_adjoints
    (F : 𝒞 ⥤ 𝒟) (m : F.CoreMonoidal)
    {C D : 𝒞} {C' D' : 𝒟}
    (β : C ⊗ D ⟶ 𝟙_ 𝒞) (β' : C' ⊗ D' ⟶ 𝟙_ 𝒟)
    (c : F.obj C ≅ C') (r : F.obj D ⟶ D')
    (b : D ≅ (ihom C).obj (𝟙_ 𝒞)) (b' : D' ≅ (ihom C').obj (𝟙_ 𝒟))
    (hb : b.hom = MonoidalClosed.curry β)
    (hb' : b'.hom = MonoidalClosed.curry β')
    (h : F.obj ((ihom C).obj (𝟙_ 𝒞)) ≅ (ihom (F.obj C)).obj (𝟙_ 𝒟))
    (heval : (F.obj C ◁ h.hom) ≫ (ihom.ev (F.obj C)).app (𝟙_ 𝒟) =
      (m.μIso C ((ihom C).obj (𝟙_ 𝒞))).hom ≫
        F.map ((ihom.ev C).app (𝟙_ 𝒞)) ≫ m.εIso.inv)
    (hpair : (c.hom ⊗ₘ r) ≫ β' = (m.μIso C D).hom ≫ F.map β ≫ m.εIso.inv) :
    (c.hom ⊗ₘ (perfectPairingDualComparison F c h).hom) ≫
        (ihom.ev C').app (𝟙_ 𝒟) =
      (m.μIso C ((ihom C).obj (𝟙_ 𝒞))).hom ≫
        F.map ((ihom.ev C).app (𝟙_ 𝒞)) ≫ m.εIso.inv ∧
    r ≫ b'.hom = F.map b.hom ≫ (perfectPairingDualComparison F c h).hom ∧
    F.map b.inv ≫ r = (perfectPairingDualComparison F c h).hom ≫ b'.inv ∧
    r = F.map b.hom ≫ (perfectPairingDualComparison F c h).hom ≫ b'.inv ∧
    ∃ rIso : F.obj D ≅ D', rIso.hom = r ∧
      rIso.inv = b'.hom ≫ (perfectPairingDualComparison F c h).inv ≫ F.map b.inv := by
  have hnorm : (c.hom ⊗ₘ (perfectPairingDualComparison F c h).hom) ≫
      (ihom.ev C').app (𝟙_ 𝒟) =
      (m.μIso C ((ihom C).obj (𝟙_ 𝒞))).hom ≫
        F.map ((ihom.ev C).app (𝟙_ 𝒞)) ≫ m.εIso.inv := by
    change (c.hom ⊗ₘ (h.hom ≫ (MonoidalClosed.pre c.inv).app (𝟙_ 𝒟))) ≫ _ = _
    rw [tensorHom_def, Category.assoc, ← MonoidalClosed.uncurry_eq,
      MonoidalClosed.uncurry_pre_app, ← Category.assoc, ← comp_whiskerRight,
      c.hom_inv_id, id_whiskerRight, Category.id_comp, MonoidalClosed.uncurry_eq]
    exact heval
  have hsquare : r ≫ b'.hom =
      F.map b.hom ≫ (perfectPairingDualComparison F c h).hom := by
    apply MonoidalClosed.uncurry_injective
    apply (cancel_epi (c.hom ▷ F.obj D)).mp
    calc
      (c.hom ▷ F.obj D) ≫ MonoidalClosed.uncurry (r ≫ b'.hom) =
          (c.hom ⊗ₘ r) ≫ β' := by
        rw [MonoidalClosed.uncurry_natural_left, hb', MonoidalClosed.uncurry_curry,
          tensorHom_def, Category.assoc]
      _ = (m.μIso C D).hom ≫ F.map β ≫ m.εIso.inv := hpair
      _ = (c.hom ▷ F.obj D) ≫ MonoidalClosed.uncurry
          (F.map b.hom ≫ (perfectPairingDualComparison F c h).hom) := by
        symm
        rw [MonoidalClosed.uncurry_natural_left, MonoidalClosed.uncurry_eq,
          ← whisker_exchange_assoc, ← tensorHom_def_assoc, hnorm,
          m.μIso_hom_natural_right_assoc, ← F.map_comp_assoc,
          ← MonoidalClosed.uncurry_eq, hb, MonoidalClosed.uncurry_curry]
  have hr : r = F.map b.hom ≫ (perfectPairingDualComparison F c h).hom ≫ b'.inv := by
    simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using
      congrArg (fun f ↦ f ≫ b'.inv) hsquare
  refine ⟨hnorm, hsquare, ?_, hr, ?_⟩
  · rw [hr]
    simp [← F.map_comp_assoc]
  · refine ⟨F.mapIso b ≪≫ perfectPairingDualComparison F c h ≪≫ b'.symm, ?_, ?_⟩
    · exact hr.symm
    · simp only [Iso.trans_inv, Iso.symm_inv, Functor.mapIso_inv, Category.assoc]

end CategoryTheory
