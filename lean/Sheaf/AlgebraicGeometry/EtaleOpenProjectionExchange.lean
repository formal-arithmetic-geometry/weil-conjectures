module

public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjectionBaseChange
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat

/-!
# Ordinary étale open projection exchange

Source: Stacks Project, Tags 0GL1, 0E8I and 03S6; blueprint
(blueprint: lem-asd-open-projection-exchange).

The displayed map identity is the constant-coefficient specialization of
`AlgebraicGeometry.Etale.derivedOpenImmersionLowerShriekProjectionIso_inv_baseChange`.
The inverse tensor and base-change isomorphisms are the canonical maps specified in the
node statement; the source's inverse normal form is used here so every factor has its
published functorial definition.
-/

@[expose] public section
set_option autoImplicit false
universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry
open Scheme
namespace Etale

/-- **Ordinary étale open tensor comparison commutes with base change.**  For an open
immersion `j : U ⟶ Z`, an arbitrary `a : Z' ⟶ Z`, `U' = pullback j a` with `u = pullback.fst`
and `j' = pullback.snd`, and arbitrary `E`, `N`, with composition read right to left,
`d_{E,N} ∘ β_{E ⊗ j^*N} ∘ a^*(γ_{j;E,N}) = γ_{j';u^*E,a^*N} ∘ (β_E ⊗ 1) ∘ t_a`, where
`γ` is the inverse of `derivedOpenImmersionLowerShriekProjectionIso`, `β` the inverse of
`derivedOpenImmersionLowerShriekBaseChangeIso` (the inverse of the sheaf mate), `t` the hom of
`leftDerivedUpperStarTensorIso`, `c_N = (derivedSquareUpperStarIso _).inv.app N`
(`= γ_{a,j'} ∘ γ_{j,u}⁻¹`) and `d_{E,N} = j'_!((1 ⊗ c_N) ∘ t_u)`, written as two factors.

Source: Stacks Project, Tag 0GL1 (sites-cohomology.tex, lemma-j-shriek-and-tensor), with the
sheaf map of Tag 0E8I (sites-modules.tex, lemma-j-shriek-and-tensor) and Tag 03S6
(etale-cohomology.tex, lemma-shriek-base-change); the equation is an agent extraction from
`derivedOpenImmersionLowerShriekProjectionIso_inv_baseChange`
(OpenImmersionLowerShriekProjectionBaseChange.lean, lines 270-301).

Proof (blueprint).
1. Fix the maps: each `t_h` is invertible (lem-kun-inverse-image-monoidal), `c` is the
   canonical composition comparison (lem-kun-derived-pullback-composition-monoidal),
   `B_E = β_E⁻¹` (sbc-prop-extension-by-zero-and-arbitrary-base-change, in the mate direction
   of def-weil-pbc-etale-shriek-base-change-map) and `π_j = γ_j⁻¹`
   (lem-pur-etale-open-derived-tensor).
2. The square is Cartesian, so lem-asd-open-base-change-unit-mate gives
   `j'^*(B_E) ∘ η'_{u^*E} = c_{j_!E} ∘ u^*(η_E)`: the first hypothesis of the categorical mate
   lemma with `F₁ = j_!`, `G₁ = j^*`, `F₂ = j'_!`, `G₂ = j'^*`, `P = u^*`, `Q = a^*`, `b = B`,
   `τ = c`.
3. With `w = j ∘ u = a ∘ j'`, two instances of the monoidality equation of
   lem-kun-derived-pullback-composition-monoidal, for `(j,u)` and `(a,j')`, eliminate `t_w`:
   `j'^*(t_a) ∘ c_{X⊗Y} ∘ u^*(t_j⁻¹) = t_{j'}⁻¹ ∘ (1 ⊗ c_Y) ∘ (c_X ⊗ 1) ∘ t_u` for all
   `X, Y` on `Z`: the second hypothesis of the mate lemma.
4. lem-asd-adjunction-projection-map-mate, with the data of steps 2-3, gives at `(E, N)`,
   `R = E ⊗ j^*N`: `t_a ∘ a^*(π_j) ∘ B_R = (B_E ⊗ 1) ∘ π_{j'} ∘ d_{E,N}`; its projection map
   is the transpose of `(η ⊗ 1)` followed by `t_j⁻¹`, that is `π_j`.
5. Every `B` and `π` is invertible; postcomposing with `γ_{j'} ∘ (β_E ⊗ 1)` and precomposing
   with `β_R ∘ a^*(γ_j)` cancels them and gives the displayed equation, natural in `E, N`.
(blueprint: lem-asd-open-projection-exchange) -/
theorem ordinaryOpenProjectionExchange_forward
    (C : Type (u + 1)) [CommRing C]
    {U Z Z' : Scheme.{u}} (j : U ⟶ Z) [IsOpenImmersion j]
    (a : Z' ⟶ Z)
    (E : DerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} C)))
    (N : DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} C))) :
    L((a)^*[ModuleCat.{u + 1} C]).map
          (((derivedOpenImmersionLowerShriekProjectionIso
            (ModuleCat.{u + 1} C) j).inv.app E).app N) ≫
        (derivedOpenImmersionLowerShriekBaseChangeIso
          (ModuleCat.{u + 1} C) (IsPullback.of_hasPullback j a)).inv.app
          (((-⊗ᴸ-(U)[ModuleCat.{u + 1} C]).obj E).obj
            (L((j)^*[ModuleCat.{u + 1} C]).obj N)) ≫
        D((pullback.snd j a)_!open[ModuleCat.{u + 1} C]).map
          (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} C) (pullback.fst j a) E
            (L((j)^*[ModuleCat.{u + 1} C]).obj N)).hom ≫
        D((pullback.snd j a)_!open[ModuleCat.{u + 1} C]).map
          (((-⊗ᴸ-(pullback j a)[ModuleCat.{u + 1} C]).obj
            (L((pullback.fst j a)^*[ModuleCat.{u + 1} C]).obj E)).map
            ((derivedSquareUpperStarIso (ModuleCat.{u + 1} C)
              (IsPullback.of_hasPullback j a).toCommSq).inv.app N)) =
      (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} C) a
        (D((j)_!open[ModuleCat.{u + 1} C]).obj E) N).hom ≫
        ((-⊗ᴸ-(Z')[ModuleCat.{u + 1} C]).map
          ((derivedOpenImmersionLowerShriekBaseChangeIso
            (ModuleCat.{u + 1} C) (IsPullback.of_hasPullback j a)).inv.app E)).app
        (L((a)^*[ModuleCat.{u + 1} C]).obj N) ≫
        ((derivedOpenImmersionLowerShriekProjectionIso
          (ModuleCat.{u + 1} C) (pullback.snd j a)).inv.app
          (L((pullback.fst j a)^*[ModuleCat.{u + 1} C]).obj E)).app
          (L((a)^*[ModuleCat.{u + 1} C]).obj N) := by
  have h := derivedOpenImmersionLowerShriekProjectionIso_inv_baseChange
    (ModuleCat.{u + 1} C) (IsPullback.of_hasPullback j a) E N
  rw [← cancel_epi (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} C) a
    (D((j)_!open[ModuleCat.{u + 1} C]).obj E) N).inv, Iso.inv_hom_id_assoc]
  rw [reassoc_of% h]
  simp only [← Functor.map_comp, Iso.inv_hom_id_assoc, Iso.hom_inv_id_app]
  erw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.comp_id]

end Etale
end AlgebraicGeometry
