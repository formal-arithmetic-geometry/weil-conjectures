module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.Topology.Sober
public import Mathlib.Topology.Irreducible

import Mathlib.AlgebraicGeometry.Properties
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion

/-!
# Separated local isomorphisms injective on generic points

Source: Stacks Project, Varieties, Tag 09NG, lemma-characterize-open-immersion;
used in the final paragraph of Tag 09NI
(blueprint: lem-trf-separated-local-isomorphism-generic-injectivity).
-/

@[expose] public section

universe u v

set_option autoImplicit false

open CategoryTheory

namespace AlgebraicGeometry

/-- A separated morphism covered on its source by open immersions is an open immersion
if it is injective on the generic points of the source's irreducible components.

Source: Stacks Project, Varieties, Tag 09NG, lemma-characterize-open-immersion
(blueprint: lem-trf-separated-local-isomorphism-generic-injectivity).

Proof:
1. Given `y, y'` with common image `x`, choose charts containing them. Their images
   are open subsets of `X`; let `W` be their intersection. Choose an irreducible
   component of `X` containing `x` (lem-sc-irreducible-components-cover), with generic
   point `ξ` (lem-sc-scheme-sober). Since `ξ` specializes to `x`, it belongs to `W`.
   The two inverse chart homeomorphisms lift it to `η, η'` specializing to `y, y'`.
2. Each lift is a generic point of a component of `Y`. Indeed, choose a component
   through the lift and its generic point `ζ`. This point stays in the same chart.
   Its image specializes to `ξ`; maximality of the component with generic point `ξ`
   forces the two singleton closures to agree. Sobriety gives `g ζ = ξ`, and chart
   injectivity gives `ζ = η` (or `η'`). This uses def-weil-irreducible-components,
   lem-sc-irreducible-components-cover and lem-sc-scheme-sober.
3. Generic-point injectivity identifies `η = η'`, so this point lies in both charts.
4. The fibre product of the charts over `X` is identified with `W`. The base change
   of the closed diagonal of `g` to that fibre product is the inclusion of the
   intersection of the source charts. These identifications follow from the
   fibre-product universal property (def-pc-fibre-product) and open-immersion
   factorizations (def-weil-open-immersion). Separatedness
   (def-weil-proper-morphism) and lem-weil-pbc-closed-immersion-base-change make
   this a closed immersion. Hence its image is closed in `W`
   (def-weil-closed-immersion); it contains `ξ`, and therefore also `x`.
5. Lift `x` into the source-chart intersection. Injectivity of each chart identifies
   this lift with both `y` and `y'`. Thus `g` is injective on all points. Apply
   lem-weil-pbc-open-immersion-injective-local-source using the given charts.
   The argument includes the empty source and uses neither reducedness nor any
   finiteness assumption on the cover or the components.
-/
theorem isOpenImmersion_of_separated_of_generic_injOn
    {Y X : Scheme.{u}} (g : Y ⟶ X) [IsSeparated g]
    {I : Type v} (V : I → Y.Opens)
    (hcover : ∀ y : Y, ∃ i : I, y ∈ V i)
    (hlocal : ∀ i : I, IsOpenImmersion ((V i).ι ≫ g))
    (hgeneric : Set.InjOn g (genericPoints Y)) :
    IsOpenImmersion g := by
  sorry

end AlgebraicGeometry
