module

public import Sheaf.AlgebraicGeometry.GroupoidScheme
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Sheaf.AlgebraicGeometry.FieldGroupoidPointTranslation

/-!
# Open images of field groupoid morphisms are closed

Source: Stacks Project, More on Groupoids, Tag 04Q6, in Situation 04Q5
(blueprint: lem-sfb-field-groupoid-open-image-closed).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The open image of a morphism of absolute groupoid schemes with common object
scheme `Spec k` is closed. Source: Stacks Project, Tag 04Q6, in Situation 04Q5
(blueprint: lem-sfb-field-groupoid-open-image-closed).

Proof plan, following the node:
1. Put `H = Set.range a` and take `r` in its closure. Apply
   `lem-sfb-field-groupoid-point-lift` and restrict both groupoids using
   `lem-sfb-field-groupoid-restriction-open`. The induced arrow map is Cartesian
   over `a`. By `lem-sfb-scheme-pullback-point-images`, its image is the inverse
   image of `H`. The open middle projection carries each open neighbourhood of
   the lifted point to a neighbourhood of `r` meeting `H`, so the lifted point
   remains in the closure of the new image. It suffices to treat this lifted
   point, for which both residue-field maps are isomorphisms.
2. Omit primes. The identity point belongs to `H` by `he`. The automorphism
   `L_r` of `lem-sfb-field-groupoid-point-translation` sends that point to `r`.
   Thus `L_r(H)` is an open neighbourhood of `r`. It meets `H`, so choose
   `x` in `H` with `L_r(x)` also in `H`.
3. Compatibility with inversion and the inverse laws give `i₂(H) = H`.
   The canonical map on composable pairs has image precisely the points whose
   two projections lie in `H`, by `lem-sfb-scheme-pullback-point-images`.
   The morphism with components `(L_r, i₂)` exists by the source and target
   identities. Its value at `x` therefore lifts to a composable pair in `R₁`.
   Associativity, inverse and unit laws show that composing this pair's image
   gives `r`: on test points, `c₂(c₂(u t₂(w), w), i₂(w)) = u t₂(w)`.
   Compatibility `hc` now puts `r` in `H`. Hence the closure of `H` is `H`.

No finite-type, separatedness, quasi-compactness or perfectness assumption is used.
The maps `s₁,t₁` and `s₂,t₂` need not coincide. -/
theorem fieldGroupoid_isClosed_range_of_isOpen
    (k : Type u) [Field k] {R₁ R₂ : Scheme.{u}}
    (s₁ t₁ : R₁ ⟶ Spec (CommRingCat.of k))
    (e₁ : Spec (CommRingCat.of k) ⟶ R₁) (i₁ : R₁ ⟶ R₁)
    (c₁ : pullback s₁ t₁ ⟶ R₁) (h₁ : IsGroupoidScheme s₁ t₁ e₁ i₁ c₁)
    (s₂ t₂ : R₂ ⟶ Spec (CommRingCat.of k))
    (e₂ : Spec (CommRingCat.of k) ⟶ R₂) (i₂ : R₂ ⟶ R₂)
    (c₂ : pullback s₂ t₂ ⟶ R₂) (h₂ : IsGroupoidScheme s₂ t₂ e₂ i₂ c₂)
    (a : R₁ ⟶ R₂) (hs : a ≫ s₂ = s₁) (ht : a ≫ t₂ = t₁)
    (he : e₁ ≫ a = e₂) (hi : i₁ ≫ a = a ≫ i₂)
    (hc : c₁ ≫ a =
      pullback.map s₁ t₁ s₂ t₂ a a (𝟙 (Spec (CommRingCat.of k)))
        ((Category.comp_id s₁).trans hs.symm) ((Category.comp_id t₁).trans ht.symm) ≫ c₂)
    (hopen : IsOpen (Set.range a)) : IsClosed (Set.range a) := by
  sorry

end AlgebraicGeometry
