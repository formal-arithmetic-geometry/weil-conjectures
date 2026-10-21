/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import Sheaf.AlgebraicGeometry.Modules.ExteriorSheaf
public import WeilConjectures.AlgebraicGeometry.Modules.TensorSection
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Sheaf.AlgebraicGeometry.Modules.ExteriorSheafTopInvertible
import WeilConjectures.AlgebraicGeometry.Modules.DeterminantShortExactExists
import Sheaf.AlgebraicGeometry.Modules.ExteriorSheafPowerComparison

/-!
# Determinants in short exact sequences

Source: blueprint, `sec-picard-framework/sk-thm-picard-rr/lem-sc-riemann-roch.md`,
proof of (*), determinant paragraph (blueprint: lem-sc-determinant-short-exact).
-/

@[expose] public section

universe v

open CategoryTheory Opposite MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false in
private theorem exteriorSheafPowerIso_hom_wedge {X : Scheme.{v}} (M : X.Modules) (n : ℕ)
    (U : X.Opens) (a : Fin n → M.val.obj (op U)) :
    (exteriorSheafPowerIso M n).hom.app U (exteriorSheafSection M n U a) =
      wedge (M := M) (r := n) (U := U) a := by
  rw [← exteriorSheafPowerIso_inv_wedge M n U a]
  exact inv_app_hom_app_apply_of_iso (exteriorSheafPowerIso M n).symm _

/-- Determinant lines are invertible and multiplicative, with the canonical isomorphism
characterized on wedges on every open subset. The inverse sends a tensor of wedges to the
wedge of the included sections followed by any lifts of the quotient sections. Since it is
a morphism of sheaves, it commutes with restriction; its characterization uses every open.

Source: blueprint, Riemann--Roch, proof of (*), determinant paragraph
(blueprint: lem-sc-determinant-short-exact).

Proof: (1) Apply `lem-sc-local-splitting-finite-free` locally and refine using
`def-amb-finite-locally-free-module` to trivialize the outside terms with ranks `r₁` and `r₃`.
(2) Apply `lem-sc-exterior-top-direct-sum` and `lem-weil-pbc-exterior-power-free-basis` on
these opens; the top exterior powers are free of rank one and the direct-sum identification
is the displayed wedge formula. (3) Two splittings differ by a map into the first term.
Expanding the changed wedge gives terms with `r₁ + 1` factors in a rank-`r₁` free module,
which vanish by `lem-weil-pbc-exterior-power-free-basis`. Thus the map is independent of
lifts, agrees on overlaps, and glues to the canonical isomorphism. Pure wedges and their
tensors generate locally, giving uniqueness. Empty wedges give the rank-zero convention
by `exteriorSheaf_zero_iso`. No sign is introduced: first-term factors precede quotient
factors, as in the source. -/
theorem determinant_shortExact {X : Scheme.{v}} (S : ShortComplex X.Modules)
    (hS : S.ShortExact) (r₁ r₂ r₃ : ℕ) (hr : r₂ = r₁ + r₃)
    [S.X₁.IsFiniteLocallyFreeOfRank r₁] [S.X₂.IsFiniteLocallyFreeOfRank r₂]
    [S.X₃.IsFiniteLocallyFreeOfRank r₃] :
    (exteriorSheaf S.X₁ r₁).IsInvertible ∧
    (exteriorSheaf S.X₂ r₂).IsInvertible ∧
    (exteriorSheaf S.X₃ r₃).IsInvertible ∧
    ∃! e : exteriorSheaf S.X₂ r₂ ≅ exteriorSheaf S.X₁ r₁ ⊗ exteriorSheaf S.X₃ r₃,
      ∀ (U : X.Opens) (a : Fin r₁ → S.X₁.val.obj (op U))
        (b : Fin r₃ → S.X₃.val.obj (op U)) (c : Fin r₃ → S.X₂.val.obj (op U)),
        (∀ i, S.g.val.app (op U) (c i) = b i) →
        e.inv.val.app (op U)
          (tmulSection (exteriorSheafSection S.X₁ r₁ U a)
            (exteriorSheafSection S.X₃ r₃ U b)) =
          exteriorSheafSection S.X₂ r₂ U
            (fun i => Fin.append (fun j => S.f.val.app (op U) (a j)) c (Fin.cast hr i)) := by
  refine ⟨exteriorSheaf_top_isInvertible S.X₁ r₁,
    exteriorSheaf_top_isInvertible S.X₂ r₂,
    exteriorSheaf_top_isInvertible S.X₃ r₃, ?_⟩
  obtain ⟨e₀, he₀⟩ := determinant_shortExact_exists S hS r₁ r₂ r₃ hr
  let eA := tensorIso (C := X.Modules) (exteriorSheafPowerIso S.X₁ r₁)
    (exteriorSheafPowerIso S.X₃ r₃)
  let eB := exteriorSheafPowerIso S.X₂ r₂
  let e := eB ≪≫ e₀ ≪≫ eA.symm
  have he : ∀ (U : X.Opens) (a : Fin r₁ → S.X₁.val.obj (op U))
      (b : Fin r₃ → S.X₃.val.obj (op U)) (c : Fin r₃ → S.X₂.val.obj (op U)),
      (∀ i, S.g.val.app (op U) (c i) = b i) →
      e.inv.val.app (op U)
          (tmulSection (exteriorSheafSection S.X₁ r₁ U a)
            (exteriorSheafSection S.X₃ r₃ U b)) =
        exteriorSheafSection S.X₂ r₂ U
          (fun i ↦ Fin.append (fun j ↦ S.f.val.app (op U) (a j)) c (Fin.cast hr i)) := by
    intro U a b c hc
    change (exteriorSheafPowerIso S.X₂ r₂).inv.app U
      (e₀.inv.app U ((((exteriorSheafPowerIso S.X₁ r₁).hom ⊗ₘ
        (exteriorSheafPowerIso S.X₃ r₃).hom).app U)
          (tmulSection (exteriorSheafSection S.X₁ r₁ U a)
            (exteriorSheafSection S.X₃ r₃ U b)))) = _
    rw [tensorHom_app_tmulSection, exteriorSheafPowerIso_hom_wedge,
      exteriorSheafPowerIso_hom_wedge]
    exact (congrArg ((exteriorSheafPowerIso S.X₂ r₂).inv.app U)
      (he₀ U a b c hc)).trans (exteriorSheafPowerIso_inv_wedge S.X₂ r₂ U _)
  refine ⟨e, he, ?_⟩
  intro e' he'
  apply Iso.ext_inv
  have := hS.epi_g
  apply exteriorSheafTensor_lift_hom_ext S.g r₁ r₃
  intro U a c
  exact (he' U a (fun i ↦ S.g.val.app (op U) (c i)) c (fun _ ↦ rfl)).trans
    (he U a (fun i ↦ S.g.val.app (op U) (c i)) c (fun _ ↦ rfl)).symm

end AlgebraicGeometry.Scheme.Modules
