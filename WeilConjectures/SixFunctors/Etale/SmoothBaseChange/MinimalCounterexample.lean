/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib

/-!
# Minimal counterexamples occur over a point

This file states the reduction step of the smooth base change theorem which says that a
property `P` of quasi-compact quasi-separated schemes over a fixed quasi-compact
quasi-separated base `T`, which is invariant under thickenings, compatible with cofiltered
limits along affine transition morphisms, and which propagates from a scheme to an open
subscheme or to its closed complement, holds for the spectrum of a field over `T` as soon as
it holds for `T` itself.  Applied to the failure locus of a base-change map, this says that a
minimal counterexample can be found over a point.

Since Mathlib has no notion of a thickening of schemes, a thickening is spelled out as a
closed immersion which is surjective on points.

## Main statements

- `AlgebraicGeometry.exists_spec_field_of_isStableUnderThickening`: blueprint `sk-lem-minimal`.

## References

- Stacks Project, Tag `0F06`, <https://stacks.math.columbia.edu/tag/0F06>
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- Blueprint `sk-lem-minimal`: Minimal counterexamples occur over a point

Let `T` be a quasi-compact quasi-separated scheme and let `P` be a property of quasi-compact
quasi-separated schemes over `T`, i.e. a predicate on morphisms `T' ⟶ T` with `T'` qcqs.
Assume that

* `hthick`: `P` is invariant under thickenings, that is, if `i : T₁ ⟶ T₂` is a closed
  immersion which is surjective on points and `f₂ : T₂ ⟶ T`, then `P (i ≫ f₂)` holds if and
  only if `P f₂` does;
* `hlimit`: `P` is compatible with cofiltered limits with affine transition morphisms, that
  is, if `D : I ⥤ Scheme` is a cofiltered diagram of qcqs schemes over `T` whose transition
  morphisms are affine, `c` is a limit cone on `D` and `g : c.pt ⟶ T` is the induced
  morphism, then `P (t.app i)` for all `i` implies `P g`;
* `hsplit`: if `V` is a quasi-compact open of a qcqs scheme `T'` over `T` and `i : Z ⟶ T'` is
  a closed immersion onto the complement of `V`, then `P` for `T' ⟶ T` implies `P` for
  `V ⟶ T` or for `Z ⟶ T`.

Then `P (𝟙 T)` implies that `P` holds for some morphism `Spec K ⟶ T` with `K` a field. -/
@[stacks 0F06]
theorem exists_spec_field_of_isStableUnderThickening (T : Scheme.{u})
    [CompactSpace T] [QuasiSeparatedSpace T]
    (P : ⦃T' : Scheme.{u}⦄ → (T' ⟶ T) → Prop)
    (hthick : ∀ {T₁ T₂ : Scheme.{u}} [CompactSpace T₂] [QuasiSeparatedSpace T₂]
      (i : T₁ ⟶ T₂) [IsClosedImmersion i], Function.Surjective i.base →
      ∀ f₂ : T₂ ⟶ T, P (i ≫ f₂) ↔ P f₂)
    (hlimit : ∀ {I : Type u} [Category.{u} I] [IsCofiltered I] (D : I ⥤ Scheme.{u})
      [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]
      [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
      (t : D ⟶ (Functor.const I).obj T) (c : Cone D), IsLimit c →
      ∀ g : c.pt ⟶ T, (∀ i, c.π.app i ≫ t.app i = g) → (∀ i, P (t.app i)) → P g)
    (hsplit : ∀ {T' Z : Scheme.{u}} [CompactSpace T'] [QuasiSeparatedSpace T']
      (f : T' ⟶ T) (V : T'.Opens), IsCompact (V : Set T') →
      ∀ (i : Z ⟶ T') [IsClosedImmersion i], Set.range i.base = (V : Set T')ᶜ →
      P f → P (V.ι ≫ f) ∨ P (i ≫ f))
    (hP : P (𝟙 T)) :
    ∃ (K : Type u) (_ : Field K) (g : Spec (CommRingCat.of K) ⟶ T), P g := by
  sorry

end AlgebraicGeometry
