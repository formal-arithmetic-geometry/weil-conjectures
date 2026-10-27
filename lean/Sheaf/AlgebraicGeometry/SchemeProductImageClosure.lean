module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.AlgebraicGeometry.Fiber

/-!
# Closure of a product image over a field

Source: Stacks Project, Varieties, Tag 04Q0 (lemma-closure-image-product-map),
using Tag 047B (lemma-closure-of-product).
(blueprint: lem-sfb-scheme-product-image-closure)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

open Scheme.IdealSheafData

/-- Over a field, the closure of a product image is the image of the product of the
reduced induced closed image closures. Source: Stacks Project, Varieties, Tag 04Q0,
with the proof of Tag 047B. (blueprint: lem-sfb-scheme-product-image-closure)

The inclusions on the right are the canonical `vanishingIdeal.subschemeι` for the
closed sets `TopologicalSpace.Closeds.closure (Set.range f)` and likewise for `g`,
as characterized by `lem-weil-pbc-reduced-induced-closed-subscheme`.

Proof plan, following the four steps of the node:
1. Put F = range f and G = range g. By `lem-sfb-scheme-pullback-point-images`,
   the product image E is the intersection of the inverse images of F and G under
   the target projections. The same formula and
   `lem-weil-pbc-reduced-induced-closed-subscheme` identify the image H on the right
   with the intersection of the inverse images of their closures. Thus H is closed,
   contains E, and contains its closure.
2. The inclusions of the reduced closures are homeomorphisms onto their images
   (`def-weil-closed-immersion`). The inverse images F₀ and G₀ of F and G are dense.
   An open subset O of the target meeting H pulls back to a nonempty open W in
   the product of the two reduced closures.
3. The first projection is open by `lem-sc-scheme-over-field-universally-open`.
   Its image of W meets F₀, say at c. The scheme-theoretic fibre at c
   (`def-pc-scheme-fibre`) is the product of Spec κ(c) with the second reduced
   closure by `def-pc-fibre-product`. The nonempty open induced by W in this
   fibre has open image in the second reduced closure, by the same openness
   lemma, so that image meets G₀.
4. Choose a point of W over such a pair. The image formula of step 1 puts its
   image in E and also in O. Thus every open meeting H meets E, giving the
   reverse inclusion H ⊆ closure E. If H is empty, step 1 already proves the
   equality. No finiteness, reducedness or separatedness assumption is used. -/
theorem closure_range_pullback_map_over_field
    (k : Type u) [Field k] {A B X Y : Scheme.{u}}
    (a : A ⟶ Spec (CommRingCat.of k)) (b : B ⟶ Spec (CommRingCat.of k))
    (x : X ⟶ Spec (CommRingCat.of k)) (y : Y ⟶ Spec (CommRingCat.of k))
    (f : A ⟶ X) (g : B ⟶ Y) (hf : f ≫ x = a) (hg : g ≫ y = b) :
    closure (Set.range (pullback.map a b x y f g (𝟙 (Spec (CommRingCat.of k)))
      ((Category.comp_id a).trans hf.symm) ((Category.comp_id b).trans hg.symm))) =
    Set.range (pullback.map
      ((vanishingIdeal (TopologicalSpace.Closeds.closure (Set.range f))).subschemeι ≫ x)
      ((vanishingIdeal (TopologicalSpace.Closeds.closure (Set.range g))).subschemeι ≫ y)
      x y
      (vanishingIdeal (TopologicalSpace.Closeds.closure (Set.range f))).subschemeι
      (vanishingIdeal (TopologicalSpace.Closeds.closure (Set.range g))).subschemeι
      (𝟙 (Spec (CommRingCat.of k))) (Category.comp_id _) (Category.comp_id _)) := by
  sorry

end AlgebraicGeometry
